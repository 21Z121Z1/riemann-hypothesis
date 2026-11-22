import Development.EtaleCohomology.EtaleTrace.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

-- bundled from Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionsDeterminedByPointsOfProper
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def TorsionH0PointGenerated : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  (∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
    ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a

def EtaleTateTwistSectionsDeterminedByPointsOfProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    ((∀ y : Pt p, Sec.res y.1 s = 0) → s = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

theorem base_gives_h0_locally_constant (hB : Base) : A9 := hB.1.2.2.2.2.2.2.2.2.2.2.2.1

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.FibrePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenEtale : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ V : P.Opens, (V : Set P).Nonempty ∧ Etale (π ∣_ V)

def RatPtIn : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {P : Scheme.{0}} (r : P ⟶ S k), LocallyOfFiniteType r →
  ∀ V : P.Opens, (V : Set P).Nonempty → ∃ t : Pt r, ∀ x, t.1.base x ∈ V

def FibreOfEtale : Prop := ∀ (k : Type) [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p →
  ∀ V : P.Opens, Etale (π ∣_ V) → ∀ t : Pt r, (∀ x, t.1.base x ∈ V) → Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem Fibre_of (h1 : GenEtale) (h2 : RatPtIn) (h3 : FibreOfEtale) : Fibre := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨V, hV, hE⟩ := h1 k p r π hπ hr hfin hsurj hun
  obtain ⟨t, ht⟩ := h2 k r hr V hV
  exact ⟨t, h3 k p r π hπ V hE t ht⟩

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.FieldDimPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem finrank_frac_of_stdSmooth (k R K : Type) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d k R] :
    Module.finrank K Ω[K⁄k] = d := by
  have : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.IsStandardSmooth k R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : Module.Free R Ω[R⁄k] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hr : Module.rank R Ω[R⁄k] = d := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d
  have hf : Module.finrank R Ω[R⁄k] = d := Module.finrank_eq_of_rank_eq hr
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K).finrank_eq, Module.finrank_baseChange, hf]

theorem FieldDim_of : FieldDim := by
  intro k _ d X _ p hp
  letI := (kHom p).toAlgebra
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := hp.exists_isStandardSmoothOfRelativeDimension (genericPoint X)
  have hUtop : U = ⊤ := by
    have hs : Subsingleton (PrimeSpectrum k) := inferInstance
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hy : p.base (genericPoint X) ∈ U := e hx
    exact (show y = p.base (genericPoint X) from hs.elim _ _) ▸ hy
  subst hUtop
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension d := by
    have := hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact this
  letI : Algebra k Γ(X, V) := ψ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, V) := hψ
  haveI : IsScalarTower k Γ(X, V) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    have key : Scheme.Hom.appTop p ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        Scheme.Hom.appLE p ⊤ V e ≫ X.germToFunctionField V := by
      rw [Scheme.Hom.appLE, Category.assoc]
      exact (congrArg (Scheme.Hom.app p ⊤ ≫ ·) (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hx)).symm
    simp only [RingHom.algebraMap_toAlgebra, kHom, ψ]
    have H : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e) ≫ X.germToFunctionField V := by
      rw [Category.assoc, ← key]
    exact congrArg (fun f => CommRingCat.Hom.hom f c) H
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  exact finrank_frac_of_stdSmooth k Γ(X, V) X.functionField d

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenInPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

abbrev A (k : Type) [Field k] (N : ℕ) := homogeneousSubmodule (Fin (N + 1)) k

theorem X_mem (k : Type) [Field k] (N : ℕ) (j : Fin (N + 1)) : (X j : MvPolynomial (Fin (N + 1)) k) ∈ A k N 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k j)

theorem X_mem' (k : Type) [Field k] (N : ℕ) (j : Fin (N + 1)) :
    (X j : MvPolynomial (Fin (N + 1)) k) ∈ A k N (1 • 1) := by
  simpa using X_mem k N j

theorem genCover {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) :
    ∃ i : Fin (N + 1), genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) := by
  have htop : ⨆ i, Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, X_mem k N i⟩
    · rw [eq_top_iff]
      intro x hxt; clear hxt
      have hx : x ∈ Algebra.adjoin k (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k)) := by
        rw [MvPolynomial.adjoin_range_X]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem y hy => exact Algebra.subset_adjoin hy
      | algebraMap c =>
        have h0 : (C c : MvPolynomial (Fin (N + 1)) k) ∈ A k N 0 :=
          (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ c)
        have := (Algebra.adjoin (A k N 0) (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k))).algebraMap_mem
          (⟨C c, h0⟩ : A k N 0)
        simpa using this
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
  have hm : ι.base (genericPoint X) ∈ (⨆ i, Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) := by
    rw [htop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  exact ⟨i, hi⟩

def away {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) : X.functionField :=
  X.presheaf.germ _ (genericPoint X) h (ι.app _
    (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg)))

def coordAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) (i : Fin (N + 1))
    (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) : Fin (N + 1) → X.functionField :=
  fun j => away ι (MvPolynomial.X i) (X_mem k N i) h 1 (MvPolynomial.X j) (X_mem' k N j)

def GenAwayEval : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∀ (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i))
  (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)),
  away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = eval₂ (kHom p) (coordAt ι i h) g

def GenOfAway : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∀ (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)),
  (∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)),
    away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = eval₂ (kHom p) (coordAt ι i h) g) →
  Gen p ι (coordAt ι i h)

end LateralTheory.EtaleTrace.Cov.GenInPf

namespace LateralTheory.EtaleTrace.Cov
open GenInPf in
theorem GenIn_of (hE : GenAwayEval) (hG : GenOfAway) : GenIn := by
  intro k _ X _ p N ι hp
  obtain ⟨i, h⟩ := genCover ι
  have hgen := hG k p N ι hp i h (hE k p N ι hp i h)
  refine ⟨coordAt ι i h, i, ?_, hgen⟩
  have h1 := (hgen 1 one_pos (MvPolynomial.X i) (X_mem k N i)).1.mp h
  have h2 := (hgen 1 one_pos (MvPolynomial.X i) (X_mem k N i)).2 1 (MvPolynomial.X i) (X_mem' k N i) h
  simp only [eval₂_X, pow_one] at h1 h2
  change coordAt ι i h i * coordAt ι i h i = coordAt ι i h i at h2
  exact mul_left_cancel₀ h1 (h2.trans (mul_one _).symm)

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOutPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOn {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ}
    (w : Fin (N + 1) → X.functionField) (U : X.Opens) (πU : U.toScheme ⟶ PN k N) : Prop :=
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h (πU.app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

def GenOutChart : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

def GenOutGlue : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField),
  (∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

theorem GenOut_of (h1 : GenOutChart) (h2 : GenOutGlue) : GenOut := by
  intro k _ X _ p N w hw
  exact h2 k p N w (h1 k p N w hw)

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenUsePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma genUse_generic_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

lemma genUse_ne {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) (hG : Gen p ι v) (n : ℕ) (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f.IsHomogeneous n) (x : X) (hx : x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f) : eval₂ (kHom p) v f ≠ 0 :=
  ((hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).1).mp (genUse_generic_mem _ x hx)

def GenUseLoc : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k,
  f.IsHomogeneous n → ∀ x : X, x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f →
  ∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x

def GenUseBack : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k,
  f.IsHomogeneous n → ∀ x : X, eval₂ (kHom p) v f ≠ 0 →
  (∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x) →
  x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f

def GenUseRangeTo : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ z : X.functionField, z ∈ (ι.stalkMap (genericPoint X)).hom.range →
  ∃ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n ∧ g.IsHomogeneous n ∧
    eval₂ (kHom p) v f ≠ 0 ∧ z = eval₂ (kHom p) v g / eval₂ (kHom p) v f

def GenUseRangeOf : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n →
  g.IsHomogeneous n → eval₂ (kHom p) v f ≠ 0 →
  eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ (ι.stalkMap (genericPoint X)).hom.range

theorem genUseLoc : GenUseLoc := by
  intro k _ X _ p N ι v hG n hn f hf x hx g hg
  have hne := genUse_ne p ι v hG n hn f hf x hx
  have hη := genUse_generic_mem _ x hx
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k (1 • n) := by
    rw [one_smul]; exact (mem_homogeneousSubmodule _ _).mpr hg
  have key := (hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).2 1 g hg' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen _ f) := ⟨⟨x, hx⟩⟩
  refine ⟨X.presheaf.germ _ x hx (ι.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule _ _).mpr hf) 1 g hg'))), ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff hne]
  rw [pow_one] at key
  exact key

theorem genUseRangeOf_pos {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) (hG : Gen p ι v) (n : ℕ) (hn : 0 < n) (f g : MvPolynomial (Fin (N + 1)) k)
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (hne : eval₂ (kHom p) v f ≠ 0) :
    eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ (ι.stalkMap (genericPoint X)).hom.range := by
  have hη := ((hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).1).mpr hne
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k (1 • n) := by
    rw [one_smul]; exact (mem_homogeneousSubmodule _ _).mpr hg
  have key := (hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).2 1 g hg' hη
  rw [pow_one] at key
  refine ⟨(PN k N).presheaf.germ _ (ι (genericPoint X)) hη (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule _ _).mpr hf) 1 g hg')), ?_⟩
  rw [eq_div_iff hne, ← key]
  erw [Scheme.Hom.germ_stalkMap_apply]

def GenUseNZ : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∃ i, v i ≠ 0

theorem genUseNZ : GenUseNZ := by
  intro k _ X _ p N ι v hG
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : ι (genericPoint X) ∈ (⊤ : (PN k N).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, ?_⟩
  have := ((hG 1 one_pos (MvPolynomial.X i) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))).1).mp hi
  simpa using this

theorem genUseRangeOf_of (hZ : GenUseNZ) : GenUseRangeOf := by
  intro k _ X _ p N ι v hG n f g hf hg hne
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨i, hi⟩ := hZ k p N ι v hG
    have h1 : (MvPolynomial.X i * f).IsHomogeneous 1 := by simpa using (isHomogeneous_X k i).mul hf
    have h2 : (MvPolynomial.X i * g).IsHomogeneous 1 := by simpa using (isHomogeneous_X k i).mul hg
    have hne' : eval₂ (kHom p) v (MvPolynomial.X i * f) ≠ 0 := by simp [hi, hne]
    have := genUseRangeOf_pos p N ι v hG 1 one_pos _ _ h1 h2 hne'
    simpa [eval₂_mul, eval₂_X, mul_div_mul_left _ _ hi] using this
  · exact genUseRangeOf_pos p N ι v hG n hn f g hf hg hne

theorem genUseRangeTo : GenUseRangeTo := by
  intro k _ X _ p N ι v hG z hz
  obtain ⟨t, rfl⟩ := hz
  obtain ⟨U, hU, s, rfl⟩ := (PN k N).presheaf.exists_germ_eq t
  obtain ⟨_, ⟨h, rfl⟩, hhη, hhU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen _)) hU
  have hle : ∀ j, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (GradedRing.proj _ j h) ≤
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) h := fun j => by
    rw [Proj.basicOpen_eq_iSup_proj _ h]; exact le_iSup (fun i => Proj.basicOpen _ (GradedRing.proj _ i h)) j
  rw [Proj.basicOpen_eq_iSup_proj, TopologicalSpace.Opens.mem_iSup] at hhη
  obtain ⟨j, hj⟩ := hhη
  obtain ⟨i, hi⟩ := genUseNZ k p N ι v hG
  have hXi : ι (genericPoint X) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) :=
    ((hG 1 one_pos _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))).1).mpr (by simpa using hi)
  have hpj : GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h ∈ homogeneousSubmodule (Fin (N + 1)) k j := by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  have hfm : MvPolynomial.X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h ∈
      homogeneousSubmodule (Fin (N + 1)) k (j + 1) := by
    have := (isHomogeneous_X k i).mul ((mem_homogeneousSubmodule _ _).mp hpj)
    exact (mem_homogeneousSubmodule _ _).mpr (by rwa [Nat.add_comm 1 j] at this)
  set f := MvPolynomial.X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h with hfdef
  have hfη : ι (genericPoint X) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
    rw [hfdef, Proj.basicOpen_mul]; exact ⟨hXi, hj⟩
  have hfU : Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f ≤ U := by
    rw [hfdef, Proj.basicOpen_mul]; exact inf_le_right.trans ((hle j).trans hhU)
  have hfne := ((hG (j + 1) (Nat.succ_pos j) f hfm).1).mp hfη
  rw [← (PN k N).presheaf.germ_res_apply (homOfLE hfU) _ hfη s]
  obtain ⟨a, ha⟩ : ∃ a, Proj.awayToSection _ f a = (PN k N).presheaf.map (homOfLE hfU).op s :=
    ⟨(Proj.basicOpenIsoAway _ f hfm (Nat.succ_pos j)).inv ((PN k N).presheaf.map (homOfLE hfU).op s), by
      rw [← Proj.basicOpenIsoAway_hom _ f hfm (Nat.succ_pos j)]; simp⟩
  obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hfm a
  have key := (hG (j + 1) (Nat.succ_pos j) f hfm).2 m g hg hfη
  refine ⟨m • (j + 1), f ^ m, g, ?_, (mem_homogeneousSubmodule _ _).mp hg, by rw [eval₂_pow]; exact pow_ne_zero _ hfne, ?_⟩
  · rw [smul_eq_mul, mul_comm]; exact ((mem_homogeneousSubmodule _ _).mp hfm).pow m
  rw [← ha]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [eval₂_pow, eq_div_iff (pow_ne_zero _ hfne)]
  exact key

theorem GenUse_of (hB : GenUseBack) : GenUse := by
  have hT := genUseRangeTo
  have hL := genUseLoc
  have hO := genUseRangeOf_of genUseNZ
  intro k _ X _ p N ι v hG
  refine ⟨fun n hn f hf x => ⟨fun hx => ⟨genUse_ne p ι v hG n hn f hf x hx, hL k p N ι v hG n hn f hf x hx⟩,
    fun h => hB k p N ι v hG n hn f hf x h.1 h.2⟩, fun z => ⟨hT k p N ι v hG z, ?_⟩⟩
  rintro ⟨n, f, g, hf, hg, hne, rfl⟩
  exact hO k p N ι v hG n f g hf hg hne

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.H0LimitCoherence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.H0LimitCoherence
open LateralTheory.EtaleTrace

variable (l : ℕ) [Fact l.Prime]

def Coh : Subring (∀ m : ℕ, ZMod (l ^ m)) where
  carrier := {x | ∀ a b (h : a ≤ b), ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ a)) (x b) = x a}
  one_mem' a b h := map_one _
  mul_mem' {u v} hu hv a b h := by simp only [Pi.mul_apply, map_mul]; rw [hu a b h, hv a b h]
  zero_mem' a b h := map_zero _
  add_mem' {u v} hu hv a b h := by simp only [Pi.add_apply, map_add]; rw [hu a b h, hv a b h]
  neg_mem' {u} hu a b h := by simp only [Pi.neg_apply, map_neg]; rw [hu a b h]

def toZl : Coh l →+* ℤ_[l] :=
  PadicInt.lift (f := fun a => (Pi.evalRingHom (fun m : ℕ => ZMod (l ^ m)) a).comp (Coh l).subtype)
    (fun a b h => RingHom.ext fun x => x.2 a b h)

theorem toZModPow_toZl (x : Coh l) (m : ℕ) : PadicInt.toZModPow m (toZl l x) = x.1 m :=
  RingHom.congr_fun (PadicInt.lift_spec _ m) x

theorem coh_of_succ (x : ∀ m : ℕ, ZMod (l ^ m))
    (h : ∀ m, ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) (ZMod (l ^ m)) (x (m + 1)) = x m) : x ∈ Coh l := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp [ZMod.castHom_apply, ZMod.cast_id']
  | succ n hn ih => rw [← ih, ← h n, ← RingHom.comp_apply, ZMod.castHom_comp]

theorem tensor_form {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (z : ℚ_[l] ⊗[ℤ_[l]] M) :
    ∃ (b : ℤ_[l]) (x : M), b ≠ 0 ∧ z = ((b : ℚ_[l]))⁻¹ ⊗ₜ x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    refine ⟨b, a • m, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    try simp [div_eq_mul_inv, mul_comm]
  | add z z' ih ih' =>
    obtain ⟨b, x, hb, rfl⟩ := ih
    obtain ⟨b', x', hb', rfl⟩ := ih'
    have h1 : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
    have h2 : (b' : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
    refine ⟨b * b', b' • x + b • x', mul_ne_zero hb hb', ?_⟩
    rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def]
    congr 2 <;> simp <;> field_simp

variable {l}

abbrev lv {E : Spc} {n i : ℤ} (x : Hl l E n i) (j : ℕ) : Ht (l ^ j) E n i := x.1 j

theorem rep_of {E : Spc} (ω : Hl l E 0 0)
    (hgen : ∀ j (z : Ht (l ^ j) E 0 0), ∃ a : ℕ, z = a • lv ω j)
    (hord : ∀ j (a : ℕ), a • lv ω j = 0 → l ^ j ∣ a) :
    (∀ x : Hl l E 0 0, ∃ c : ℤ_[l], x = c • ω) ∧ ∀ c : ℤ_[l], c • ω = 0 → c = 0 := by
  have key : ∀ j (s s' : ZMod (l ^ j)), s • lv ω j = s' • lv ω j → s = s' := by
    intro j s s' h
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have h0 : (s - s').val • lv ω j = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val, sub_smul, h, sub_self]
    obtain ⟨t, ht⟩ := hord j _ h0
    have : (((s - s').val : ℕ) : ZMod (l ^ j)) = 0 := by rw [ht, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [ZMod.natCast_zmod_val] at this
    exact sub_eq_zero.1 this
  have gen : ∀ j (z : Ht (l ^ j) E 0 0), ∃ s : ZMod (l ^ j), z = s • lv ω j := by
    intro j z
    obtain ⟨a, ha⟩ := hgen j z
    exact ⟨a, by rw [Nat.cast_smul_eq_nsmul]; exact ha⟩
  have redω : ∀ j (s : ZMod (l ^ (j + 1))), red (l ^ (j + 1)) (l ^ j) E 0 0 (s • lv ω (j + 1)) =
      (ZMod.castHom (pow_dvd_pow l (Nat.le_succ j)) (ZMod (l ^ j)) s) • lv ω j := by
    intro j s
    haveI : NeZero (l ^ (j + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    conv_lhs => rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul]
    rw [map_nsmul, ZMod.castHom_apply, ZMod.cast_eq_val, Nat.cast_smul_eq_nsmul]
    exact congrArg (s.val • ·) (ω.2 j)
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · choose s hs using fun j => gen j (lv x j)
    have hc : s ∈ Coh l := coh_of_succ l s fun j => key j _ _ (by
      rw [← redω, ← hs (j + 1), ← hs j]; exact x.2 j)
    refine ⟨toZl l ⟨s, hc⟩, Subtype.ext (funext fun j => ?_)⟩
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change lv x j = (toZl l ⟨s, hc⟩) • (ω.1 j : HtL l j E 0 0)
    rw [HtL.smul_eq l j j le_rfl, toZModPow_toZl]
    change lv x j = (s j).val • lv ω j
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val]
    exact hs j
  · refine PadicInt.ext_of_toZModPow.mp fun j => ?_
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [map_zero]
    refine key j _ _ ?_
    have h1 : (c • ω).1 j = (0 : Hl l E 0 0).1 j := by rw [hc]
    change c • (ω.1 j : HtL l j E 0 0) = 0 at h1
    rw [HtL.smul_eq l j j le_rfl] at h1
    change (PadicInt.toZModPow j c).val • lv ω j = 0 at h1
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val] at h1
    rw [h1, zero_smul]

end LateralTheory.EtaleTrace.H0LimitCoherence

namespace LateralTheory.EtaleTrace

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LCompIntPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem LCompInt_of : LCompInt := by
  intro k _ _ d X p hp hc
  have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p

end LateralTheory.EtaleTrace
end
end

