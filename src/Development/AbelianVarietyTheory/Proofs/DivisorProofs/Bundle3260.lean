import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueVectorFieldOfGlobalOneFormValues
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHoms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixMat

theorem exists_locClosed_homFix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM hrA hrB hamp hk hva hbasA hbasB
  obtain ⟨eA, heA⟩ := hrA
  obtain ⟨eB, heB⟩ := hrB
  obtain ⟨mA, bA, hbA⟩ := hbasA
  obtain ⟨mB, bB, hbB⟩ := hbasB
  have hyp : Hyps L M k bA bB eA eB := ⟨hA, hB, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩

  obtain ⟨X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest, hex, hmat⟩ :=
    GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme Rg A B L M k mA mB bA bB eA eB hyp
  refine ⟨mA * mB, X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest.1, htest.2.1, htest.2.2.1,
    htest.2.2.2, ?_⟩
  intro R _ t A' B' _ _ φA' φB' Φ' h1 h2 h3 h4
  have ht : IsTest A B L M t A' B' φA' φB' Φ' := ⟨h1, h2, h3, h4⟩

  obtain ⟨c, hc'⟩ := GlobalTheory.T.line_bundle_sections_product_base_change Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' ht
  obtain ⟨h, hh, hmatc⟩ := hex R t A' B' φA' φB' Φ' c ht hc'

  obtain ⟨A₂, g₂, B₂, g₂', φA₂, φB₂, Φ₂, ht₂, hp₂⟩ :=
    GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest Rg A B L M H (Sp R) (i ≫ cE ≫ affπ Rg (mA * mB)) h AH BH φA φB Φ htest
  have hm₂ := hmat R h A₂ B₂ φA₂ φB₂ Φ₂ ht₂ hp₂
  rw [hh, hmatc] at hm₂
  rw [hh] at ht₂

  have hpd := GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data Rg A B L M k mA mB bA bB eA eB hyp R t A₂ B₂ φA₂ φB₂ Φ₂ A' B' φA' φB' Φ' c
    ht₂ ht hm₂ hc'
  have hfin := IsPullD.comp hp₂ hpd
  rw [Category.id_comp] at hfin
  refine ⟨h, ⟨hh, hfin⟩, ?_⟩

  rintro h' ⟨hh', hpd'⟩
  have ht' : IsTest A B L M (h' ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' := by
    rw [hh']; exact ht
  have hm' := hmat R h' A' B' φA' φB' Φ' ht' hpd'
  rw [hh'] at hm'
  have heq : matOf (h' ≫ i ≫ cE) = c :=
    GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' _ _ ht hm' hc'
  have hg : h' ≫ i ≫ cE = h ≫ i ≫ cE := by
    apply hom_ext_affine
    · simp only [Category.assoc]
      rw [hh', hh]
    · intro n
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective n
      exact congrFun (congrFun (heq.trans hmatc.symm) p.1) p.2
  have hg' : h' ≫ i = h ≫ i := by
    rw [← cancel_mono cE]
    simpa only [Category.assoc] using hg
  exact (cancel_mono i).1 hg'

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_pos_mul_lt_of_finite {ι : Type*} {T : Set ι} (hT : T.Finite) (A O : ι → ℚ)
    (hA : ∀ t ∈ T, 0 < A t) : ∃ c : ℚ, 0 < c ∧ ∀ t ∈ T, c * O t < A t := by
  have h : ∀ᶠ c in nhdsWithin (0 : ℚ) (Set.Ioi 0), ∀ t ∈ T, c * O t < A t :=
    (Filter.eventually_all_finite hT).2 fun t ht => by
      have h1 : Filter.Tendsto (fun c : ℚ => c * O t) (nhds 0) (nhds (0 * O t)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h1
      exact nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds (hA t ht)))
  obtain ⟨c, hc, hc'⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨c, hc', hc⟩

theorem exists_pos_kltAt_add_smul : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (B : X → ℚ), 0 < m → IsLogCanonicalMultiple p n Δ m G → (∀ y, KltAt p n Δ y) → IsQCart B → ∃ c : ℚ, 0 < c ∧ ∀ y, KltAt p n (Δ + c • B) y := by
  intro hP X _ _ _ p n hproj hn Δ m G B hm hG hklt hB
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  obtain ⟨η, hη, hGη⟩ := hG
  obtain ⟨m', D₀, hm', -, rfl⟩ := hB
  obtain ⟨S, hS, hSt⟩ := GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hproj hn η m G D₀ hη hm
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g f : X.functionFieldˣ), x ∈ U ∧
      ∀ y ∈ U, G.IsEqn y g ∧ D₀.IsEqn y f := by
    intro x
    obtain ⟨g, hg⟩ := G.exists_isEqn x
    obtain ⟨f, hf⟩ := D₀.exists_isEqn x
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    exact ⟨U ⊓ V, g, f, ⟨hU, hV⟩, fun y hy => ⟨hgU y hy.1, hfV y hy.2⟩⟩
  choose U g f hxU hUeq using hloc
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (U x : Set X))
    fun x => (U x).isOpen.mem_nhds (hxU x)
  let T : Set (DivOver p × X) := {q | q.1 ∈ S ∧ q.2 ∈ t ∧ ∃ y ∈ U q.2, q.1.Through y}
  have hT : T.Finite := (hS.prod t.finite_toSet).subset fun q hq => ⟨hq.1, hq.2.1⟩
  obtain ⟨c, hc, hcT⟩ := exists_pos_mul_lt_of_finite hT
    (fun q => discrep q.1 η m (g q.2) + 1) (fun q => (q.1.ord (f q.2) : ℚ)) (by
      rintro ⟨E, x₀⟩ ⟨-, -, y, hy, hEy⟩
      have := ((hGη y _ (hUeq x₀ y hy).1).kltAt_iff hn hη hm).1 (hklt y) E hEy
      simp only
      linarith)
  refine ⟨c * m', mul_pos hc (by exact_mod_cast hm'), fun y => ?_⟩
  obtain ⟨x₀, hx₀t, hy⟩ : ∃ x₀ ∈ t, y ∈ U x₀ := by
    have : y ∈ ⋃ x ∈ t, (U x : Set X) := ht.symm ▸ trivial
    simpa using this
  obtain ⟨hgy, hfy⟩ := hUeq x₀ y hy
  have hlog := hGη y _ hgy
  have hD : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil D₀ m' z = (E.ord (f x₀) : ℚ) / m' := by
    intro z hz E hE
    rw [qWeil, (hUeq x₀ z (hz.mem_open (U x₀).isOpen hy)).2.mult_eq, hE.ord_eq]
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ (qWeil D₀ m') η y m m' (g x₀)
    (f x₀) (c * m') hm hm' hlog hD
  refine (hlog''.kltAt_iff hn hη hm'').2 fun E hE => ?_
  rw [hdisc]
  have key := (hSt y (g x₀) (f x₀) c hgy hfy).1 (fun E' hE'S hE'y => by
    have := hcT (E', x₀) ⟨hE'S, hx₀t, y, hy, hE'y⟩
    simp only at this
    linarith) E hE
  have hm0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have : c * m' * ((E.ord (f x₀) : ℚ) / m') = c * E.ord (f x₀) := by field_simp
  linarith

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientOfGaloisStableFiniteSubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.Quot

theorem over_ext_of_pt_eq {K : Type} [Field K] {H Z : Over (Sp K)} [IsReduced H.left]
    [LocallyOfFiniteType H.hom] [IsSeparated Z.hom] (a b : H ⟶ Z)
    (h : ∀ y : ptOver K (AlgebraicClosure K) ⟶ H, y ≫ a = y ≫ b) : a = b := by
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback H.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd H.hom q)
  have hd : Dense (closedPoints ↥(pullback H.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst H.hom q).surjective.denseRange.dense_image
    (pullback.fst H.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι a.left b.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback H.hom q)) := hw₀
    let y : Sp Ω ⟶ H.left :=
      pointOfClosedPoint (pullback.snd H.hom q) w hw ≫ pullback.fst H.hom q
    have hy : y ≫ H.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : ptOver K Ω ⟶ H := Over.homMk y hy
    have hx : y ≫ a.left = y ≫ b.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι a.left b.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst H.hom q) (pointOfClosedPoint_apply (pullback.snd H.hom q) w hw _)
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom
    ((Over.w a).trans (Over.w b).symm) (equalizer.ι _ _) (equalizer.condition _ _))

end GlobalTheory.AV.Quot

namespace GlobalTheory.AV.AbVar

theorem exists_quot_of_galois_stable : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G →
    ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) →
    ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ deg q = Nat.card G ∧ (ptMap q).ker = G ∧
      ∀ (C : AbVar K) (f : A ⟶ C), G ≤ (ptMap f).ker → ∃ g : B ⟶ C, q ≫ g = f := by
  intro K _ A G hfin hn hgal
  obtain ⟨H, _, i, hi, hmono, hfinH, het, hG⟩ := GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points K A G hfin hn hgal
  obtain ⟨B, q, hq, hker⟩ := GlobalTheory.T.exists_quotient_abelianVariety_by_finiteSubgroup K A H i hi hmono hfinH
  have : IsReduced H.left := GlobalTheory.isReduced_of_smooth_of_isReduced H.hom

  have hext : ∀ (Z : Over (Sp K)) [IsSeparated Z.hom] (a b : H ⟶ Z),
      (∀ y : A.Pt, y ∈ G → ∀ (y' : ptOver K (AlgebraicClosure K) ⟶ H), y' ≫ i = y → y' ≫ a = y' ≫ b) →
      a = b := by
    intro Z _ a b hab
    exact GlobalTheory.AV.Quot.over_ext_of_pt_eq a b fun y' => hab _ ((hG _).2 ⟨y', rfl⟩) y' rfl
  have hkerG : (ptMap q).ker = G := by
    ext x
    rw [MonoidHom.mem_ker, ptMap_apply, hker, hG]
  refine ⟨B, q, hq, ?_, hkerG, ?_⟩
  · rw [GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed K A B q (Nat.card G) hn hq, hkerG]
    intro T x hx
    obtain ⟨y, rfl⟩ := (hker T x).1 hx
    have := A.ab.proper
    have hpow : i ^ Nat.card G = 1 := by
      refine hext A.X _ _ ?_
      intro z hz y' hy'
      rw [MonObj.comp_pow, hy', MonObj.comp_one]
      have h1 := pow_card_eq_one' (G := G) (x := ⟨z, hz⟩)
      exact congrArg Subtype.val h1
    rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
  · intro C f hf
    refine GlobalTheory.AV.AbVar.exists_factor_of_isogeny K A B C q f hq ?_
    intro T x hx
    obtain ⟨y, rfl⟩ := (hker T x).1 hx
    have := C.ab.proper
    have hif : i ≫ f.hom = 1 := by
      refine hext C.X _ _ ?_
      intro z hz y' hy'
      rw [← Category.assoc, hy', MonObj.comp_one]
      exact hf hz
    rw [Category.assoc, hif, MonObj.comp_one]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_threshold_lcAt_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (D B : X → ℚ) (x : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsQCart B → KltAt p n (Δ + D) x → ¬ KltAt p n (Δ + D + B) x → ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ LcAt p n (Δ + D + c • B) x ∧ ¬ KltAt p n (Δ + D + c • B) x := by
  intro hP X _ _ _ p n hp hn Δ m G D B x hm hG hD hB hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨mD, D₀, hmD, -, rfl⟩ := hD
  obtain ⟨m', B₀, hm', -, rfl⟩ := hB
  obtain ⟨η, hη, hG₁⟩ := isLogCanonicalMultiple_add_qWeil X p n Δ m mD G D₀ hm hmD hG
  have hm₁ : 0 < m * mD := Nat.mul_pos hm hmD
  obtain ⟨S, hSf, hS⟩ :=
    GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hp hn η (m * mD) (mD • G + m • D₀) B₀ hη hm₁
  obtain ⟨g, hg⟩ := (mD • G + m • D₀).exists_isEqn x
  obtain ⟨f, hf⟩ := B₀.exists_isEqn x
  have hL := hG₁ x g hg
  have hBf : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → qWeil B₀ m' z = (E.ord f : ℚ) / m' := by
    intro z hz E hE
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  obtain ⟨a, ha⟩ : ∃ a : DivOver p → ℚ, ∀ E, a E = discrep E η (m * mD) g := ⟨_, fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : DivOver p → ℚ, ∀ E, t E = (E.ord f : ℚ) / m' := ⟨_, fun _ => rfl⟩
  have hrw (c : ℚ) (E : DivOver p) :
      a E - c * t E = discrep E η (m * mD) g - c / m' * E.ord f := by
    rw [ha, ht]; ring
  have step (c : ℚ) : ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧
      IsLogEqn p (Δ + qWeil D₀ mD + c • qWeil B₀ m') η x m'' g'' ∧
      ∀ E : DivOver p, discrep E η m'' g'' = a E - c * t E := by
    obtain ⟨m'', g'', h1, h2, h3⟩ :=
      GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Δ + qWeil D₀ mD) (qWeil B₀ m') η x (m * mD) m' g f c hm₁ hm' hL hBf
    exact ⟨m'', g'', h1, h2, fun E => by rw [h3, ha, ht]⟩
  have hka : ∀ E : DivOver p, E.Through x → -1 < a E := fun E hE => by
    rw [ha]; exact (hL.kltAt_iff hn hη hm₁).1 hk E hE

  obtain ⟨E₀, hE₀S, hE₀x, hE₀⟩ : ∃ E ∈ S, E.Through x ∧ a E - 1 * t E ≤ -1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨m₁', g₁, hm₁', hL₁, hd₁⟩ := step 1
    rw [one_smul] at hL₁
    refine hnk ((hL₁.kltAt_iff hn hη hm₁').2 fun E hE => ?_)
    rw [hd₁, hrw]
    refine (hS x g f (1 / m') hg hf).1 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    exact hc E' hE' hE'x
  have hT0 : E₀ ∈ {E | E ∈ S ∧ E.Through x ∧ 0 < t E} :=
    ⟨hE₀S, hE₀x, by have := hka E₀ hE₀x; linarith⟩
  obtain ⟨E₁, ⟨hE₁S, hE₁x, hE₁t⟩, hmin⟩ :=
    Set.exists_min_image {E | E ∈ S ∧ E.Through x ∧ 0 < t E} (fun E => (1 + a E) / t E)
      (hSf.subset fun E hE => hE.1) ⟨E₀, hT0⟩
  have hE₁a := hka E₁ hE₁x
  refine ⟨(1 + a E₁) / t E₁, div_pos (by linarith) hE₁t, ?_, ?_⟩
  · refine (hmin E₀ hT0).trans ?_
    rw [div_le_one hT0.2.2]
    linarith
  obtain ⟨m'', g'', hm'', hL'', hd''⟩ := step ((1 + a E₁) / t E₁)
  refine ⟨(lcAt_iff_of_isLogEqn X p n hp hn _ η x m'' g'' hη hm'' hL'').2 fun E hE => ?_,
    fun hk' => ?_⟩
  · rw [hd'', hrw]
    refine (hS x g f ((1 + a E₁) / t E₁ / m') hg hf).2 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    by_cases htE : 0 < t E'
    · have := hmin E' ⟨hE', hE'x, htE⟩
      rw [le_div_iff₀ htE] at this
      linarith
    · have h0 : 0 ≤ (1 + a E₁) / t E₁ := (div_pos (by linarith) hE₁t).le
      have := hka E' hE'x
      nlinarith
  · have := (hL''.kltAt_iff hn hη hm'').1 hk' E₁ hE₁x
    rw [hd'', div_mul_cancel₀ _ hE₁t.ne'] at this
    linarith

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_ratio_gen_mod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  intro R _ _ _ hBase D A G _ _ hG U
  obtain ⟨k₀, hk₀, hA⟩ := GlobalTheory.T.exists_finite_theta_sections_thickening_cover R hBase D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨n, τ, hτ⟩ := hA k hk
  exact GlobalTheory.T.ratioGeneration_mod_maxIdeal_of_closedFibre R G U.LG.L k s₀ i (GlobalTheory.T.localGeneration_ratios_closedFibre_any_unit_section R G U.LG.L k n τ hτ s₀ i) e w hw hu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFinite
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GenCut

theorem exists_finite_drop {T : Type} [TopologicalSpace T] [NoetherianSpace T] (Y : Set T) (d : ℕ)
    (hY : topologicalKrullDim Y ≤ (d + 1 : ℕ)) :
    ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → topologicalKrullDim ↥(Y \ U) ≤ d := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hne : ∀ C : irreducibleComponents Y, ∃ y : Y, y ∈ C.1 := fun C => C.2.1.nonempty
  choose y hy using hne
  have : Finite (irreducibleComponents Y) := hfin.to_subtype
  refine ⟨Set.range fun C => (y C : T), Set.finite_range _, fun U hU hS => ?_⟩
  have hC : IsClosed ((Subtype.val : Y → T) ⁻¹' Uᶜ) := hU.isClosed_compl.preimage continuous_subtype_val
  have h := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero Y).1 _ (d + 1) hC hY fun Z hZ _ hsub =>
    hsub (hy ⟨Z, hZ⟩) (hS ⟨⟨Z, hZ⟩, rfl⟩)
  let f : ↥(Y \ U) → ↥((Subtype.val : Y → T) ⁻¹' Uᶜ) := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have hf : IsInducing f := by
    refine (IsInducing.subtypeVal.comp IsInducing.subtypeVal).of_comp_iff.1 ?_
    exact IsInducing.subtypeVal
  have h2 := lt_of_le_of_lt hf.topologicalKrullDim_le h
  rw [Nat.cast_add, Nat.cast_one] at h2
  exact ENat.WithBot.lt_add_one_iff.1 h2

theorem exists_sections_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  intro k _ X _ p D hp P hA d
  have := hp.isNoetherian
  induction d with
  | zero =>
    intro Z _ hd
    have hf : Finite ↥(Z ∩ fib X 0) := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X 0)).2 inferInstance (by simpa using hd)
    refine ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, ?_⟩
    exact (Set.toFinite (Z ∩ fib X 0)).subset (Set.inter_subset_inter_left _ Set.sdiff_subset)
  | succ d ih =>
    intro Z hZ hd
    obtain ⟨S, hS, hdrop⟩ := exists_finite_drop (Z ∩ fib X 0) d hd
    obtain ⟨e₀, he₀, f, hf, hSf⟩ := GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite k X p D hp P hA S hS
    have hU : IsOpen (NV P e₀ 0 f) := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e₀ 0 f hf).1
    have h := hdrop _ hU hSf
    rw [show (Z ∩ fib X 0) \ NV P e₀ 0 f = (Z \ NV P e₀ 0 f) ∩ fib X 0 from by
      ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto] at h
    obtain ⟨e, g, heg, hfin⟩ := ih _ (hZ.sdiff hU) h
    refine ⟨Fin.cons e₀ e, Fin.cons f g, fun j => ?_, hfin.subset ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨he₀, hf⟩
      · exact heg j
    · rintro x ⟨⟨hxZ, hx⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists] at hx
      refine ⟨⟨⟨hxZ, hx 0⟩, ?_⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists]
      exact fun j => hx j.succ

end GlobalTheory.HSAmp.GenCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  first | exact @GlobalTheory.GenFibreGen.exists_secs_generic | exact GlobalTheory.GenFibreGen.exists_secs_generic | (intros; apply GlobalTheory.GenFibreGen.exists_secs_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  first | exact @GlobalTheory.UMin.MapAff.theta_map_aff | exact GlobalTheory.UMin.MapAff.theta_map_aff | (intros; apply GlobalTheory.UMin.MapAff.theta_map_aff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedKernelClosedFiniteFlatAffineBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedKernel_closed_finiteFlat_affineBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  first | exact @GlobalTheory.DualCover.twistedKernel_affine | exact GlobalTheory.DualCover.twistedKernel_affine | (intros; apply GlobalTheory.DualCover.twistedKernel_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem exists_twist_of_samePol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D hS
  obtain ⟨β, xe, hβ, hc, wΛ, hwΛ, hτ⟩ := GlobalTheory.T.exists_iso_refinements_same_polarised R D₀.toPre D.toPre hS
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨b, hb, w, hw⟩ := GlobalTheory.T.exists_translate_of_mumfordBundle_match R D₀.toPre D.toPre β hβ ⟨wΛ, hwΛ⟩
  obtain ⟨g, -, h2, ht⟩ := GlobalTheory.T.exists_order_two_point_torus_extension_translate R hR D₀ D β xe hβ hc wΛ hwΛ hτ b hb w hw
  exact ⟨g, h2, ht⟩

end GlobalTheory.MumCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueVectorFieldOfGlobalOneFormValuesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : AffOp A.left) (l : GlobForm A.hom →ₗ[R] Sec A.hom U.unop.1), ∃! δ : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] Sec A.hom U.unop.1, ∀ w : GlobForm A.hom, δ (w.1 U) = l w := by
  first | exact @GlobalTheory.ParPt.exists_unique_of_globForm | exact GlobalTheory.ParPt.exists_unique_of_globForm | (intros; apply GlobalTheory.ParPt.exists_unique_of_globForm <;> assumption)
end

