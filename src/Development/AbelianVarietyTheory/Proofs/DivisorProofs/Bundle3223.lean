import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0826
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixUniv

variable {mA mB : ℕ}

theorem comb_comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) (z : X₂)
    (q : N.ι) (hq : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ : gs p₂ z ⊤ (h.appTop (c i j)) = gs (r ≫ p) z ⊤ (c i j) := by
    rw [← e]; exact gs_pull p₂ h z ⊤ trivial (c i j)
  rw [e₁, gs_comp r p z ⊤ trivial, gs_comp r φ z _ hq]

theorem Generates.comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hg : Generates a φ p c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂)
    (e : p₂ ≫ h = r ≫ p) : Generates a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) := by
  intro z q hq
  obtain ⟨j, hj⟩ := hg (r z) q hq
  exact ⟨j, by rw [comb_comp a φ p c r h p₂ e z q hq j]; exact hj.map _⟩

theorem Proport.comp {A₀ B₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {H : LB B₀} {a : Fin mA → LB.Sec N}
    {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hp : Proport a b φ p Ψ c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) :
    Proport a b (r ≫ φ) p₂ (r ≫ Ψ) (fun i j => h.appTop (c i j)) := by
  intro z q k hq hk j j'
  rw [comb_comp a φ p c r h p₂ e z q hq, comb_comp a φ p c r h p₂ e z q hq, gs_comp r Ψ z _ hk,
    gs_comp r Ψ z _ hk, ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem matOf_comp {Rg : Type} [CommRing Rg] {X X' : Scheme.{0}} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) : matOf (h ≫ g) = fun i j => h.appTop (matOf g i j) := by
  funext i j; exact coord_comp h g _

theorem relift {S T' T : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over T} [GrpObj G₁] {G' : Over T'} [GrpObj G']
    {t₁ : T ⟶ S} {u : T' ⟶ T} {φ₁ : G₁.left ⟶ G.left} {φ' : G'.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G t₁ φ₁)
    (h' : IsGrpPullback G' G (u ≫ t₁) φ') : ∃ ψ : G'.left ⟶ G₁.left, IsGrpPullback G' G₁ u ψ ∧ ψ ≫ φ₁ = φ' := by
  refine ⟨h₁.1.lift φ' (G'.hom ≫ u) (by rw [h'.1.w, Category.assoc]), ?_, h₁.1.lift_fst _ _ _⟩
  exact h₁.cancel (by rw [h₁.1.lift_fst]; exact h') (h₁.1.lift_snd _ _ _)

theorem exists_universal_matrix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH
  obtain ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ := hH
  obtain ⟨hfl, hpj, huc⟩ := GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed Rg A L hAb hL hamp
  haveI := huc
  have hEmb := GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hBb hM hk hva hbB
  have hcov : (⨆ j, nonzeroLocus (bB j)) = ⊤ := hEmb.1
  have hNA : (LPow A L (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hL _ _
  have hNB : (LPow B M (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hM _ _
  choose αA hαA using fun i => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg A L k eA (bA i) hL heA
  choose βB hβB using fun j => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg B M k eB (bB j) hM heB
  obtain ⟨U, hU⟩ := GlobalTheory.T.isOpen_generatingCombinationMatrixLocus Rg _ (fA A) _ mA mB bA hNA
  obtain ⟨ZF, ιF, hιF, hF⟩ := GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections Rg _ _ (fA A) (fA B) _ _ mA mB bA bB hfl hpj hNA
  obtain ⟨ZN, ιN, hιN, hNm⟩ := GlobalTheory.T.linearNormalisation_closed_subscheme Rg mA mB αA βB
  haveI : IsNoetherian (Sp (MvPolynomial (Fin (mA * mB)) Rg)) := isNoetherian_Spec.2 inferInstance
  obtain ⟨W, j₁, hj₁, hj₁q, hWn, hW⟩ := GlobalTheory.T.exists_immersed_closed_open_intersection _ ZF ZN ιF ιN U hιF hιN
  have cond : ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ (topS Rg ⊗ A).left)
      (p : X' ⟶ T), (∃ w, w ≫ j₁ = g) → IsPullback φ p (fA A) (g ≫ affπ Rg (mA * mB)) →
      Generates bA φ p (matOf g) ∧ FormsOK bA (fA B) bB φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ∧
        Normal (g ≫ affπ Rg (mA * mB)) (matOf g) αA βB := by
    intro T X' g φ p hg hP
    obtain ⟨h1, h2, h3⟩ := (hW T g).2 hg
    exact ⟨(hU T X' g φ p hP).2 h3, (hF T X' g φ p hP).2 h1, (hNm T g).2 h2⟩
  have datum : ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (∃ w, w ≫ j₁ = g) →
      ∃ (AT : Over T) (_ : GrpObj AT) (BT : Over T) (_ : GrpObj BT) (φA : AT.left ⟶ A.left) (φB : BT.left ⟶ B.left)
        (Φ : AT ⟶ BT), IsGrpPullback AT A (g ≫ affπ Rg (mA * mB)) φA ∧
        IsGrpPullback BT B (g ≫ affπ Rg (mA * mB)) φB ∧ IsMonHom Φ ∧ Generates bA (φA ≫ θ A) AT.hom (matOf g) ∧
        Proport bA bB (φA ≫ θ A) AT.hom (Φ.left ≫ φB ≫ θ B) (matOf g) := by
    intro T g hg
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj B) := Functor.grpObjObj
    have pA := isGrpPullback_pullback A (g ≫ affπ Rg (mA * mB))
    have pB := isGrpPullback_pullback B (g ≫ affπ Rg (mA * mB))
    have hP := (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A T _ _ _ (g ≫ affπ Rg (mA * mB))).1 pA.1
    obtain ⟨c1, c2, c3⟩ := cond T _ g _ _ hg hP
    obtain ⟨Ψ, hΨ, hpr⟩ := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ T (fA A) (fA B) _ _ mA mB bA bB _ _ _ (matOf g) hEmb hNB hNA hP.w
      c1).1 c2
    obtain ⟨Φ, hΦ, hΦΨ⟩ := GlobalTheory.T.grpHom_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB T _ _ _ _ _ Ψ (matOf g)
      ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ hαA hβB pA pB hΨ c1 hpr c3
    exact ⟨_, inferInstance, _, inferInstance, _, _, Φ, pA, pB, hΦ, c1, by rw [hΦΨ]; exact hpr⟩
  have θf : ∀ C : Over (Sp Rg), θ C ≫ fA C = C.hom := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.1
  have θi : ∀ C : Over (Sp Rg), IsIso (θ C) := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.2
  obtain ⟨A₁, iA₁, B₁, iB₁, φA₁, φB₁, Φ₁, pA₁, pB₁, hΦ₁, hg₁, hp₁⟩ := datum W j₁ ⟨𝟙 _, Category.id_comp _⟩
  haveI := hWn
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic Rg A B L M eA eB W (j₁ ≫ affπ Rg (mA * mB)) A₁ B₁ φA₁ φB₁ Φ₁ hAb hBb hL hM heA heB
    hamp pA₁ pB₁ hΦ₁
  have compare : ∀ (T : Scheme.{0}) (u : T ⟶ W) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φA' →
      IsGrpPullback B' B ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φB' →
      Generates bA (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) →
      Proport bA bB (φA' ≫ θ A) A'.hom (Φ'.left ≫ φB' ≫ θ B) (matOf (u ≫ j₁)) →
      ∃ (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left), IsGrpPullback A' A₁ u ψA ∧ IsGrpPullback B' B₁ u ψB ∧
        ψA ≫ φA₁ = φA' ∧ ψB ≫ φB₁ = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ₁.left := by
    intro T u A' B' _ _ φA' φB' Φ' hA' hB' hgen hprop
    rw [Category.assoc] at hA' hB'
    obtain ⟨ψA, hψA, eA'⟩ := relift pA₁ hA'
    obtain ⟨ψB, hψB, eB'⟩ := relift pB₁ hB'
    refine ⟨ψA, ψB, hψA, hψB, eA', eB', ?_⟩
    apply pB₁.1.hom_ext
    · rw [Category.assoc, eB', Category.assoc, ← cancel_mono (θ B), Category.assoc, Category.assoc, Category.assoc]
      have hp := hp₁.comp ψA u A'.hom hψA.1.w.symm
      rw [← matOf_comp, ← Category.assoc ψA φA₁, eA'] at hp
      refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ _ T (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) _ _ hEmb hNB hNA hgen
        hprop hp ?_
      simp only [Category.assoc, θf]
      rw [hB'.1.w, pB₁.1.w, reassoc_of% (Over.w Φ'), reassoc_of% (Over.w Φ₁), reassoc_of% hψA.1.w]
    · rw [Category.assoc, hψB.1.w, reassoc_of% (Over.w Φ'), Category.assoc, Over.w Φ₁, hψA.1.w]
  obtain ⟨AH, iAH, BH, iBH, φAH, φBH, ΦH, pAH, pBH, hΦH, hgH, hpH⟩ := datum Z (i ≫ j₁) ⟨i, rfl⟩
  obtain ⟨ψA, ψB, hψA, hψB, eψA, eψB, eΦ⟩ := compare Z i AH BH φAH φBH ΦH pAH pBH hgH hpH
  have hlb : LBIso (L.pull φAH) ((M.pull φBH).pull ΦH.left) := by
    have := (hZ Z i AH BH ψA ψB ΦH hψA hψB eΦ).2 ⟨𝟙 _, Category.id_comp _⟩
    rwa [eψA, eψB] at this
  refine ⟨(i ≫ j₁).image, (i ≫ j₁).imageι, Z, (i ≫ j₁).toImage, AH, iAH, BH, iBH, φAH, φBH, ΦH, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.toImage_imageι_assoc]
    exact ⟨pAH, pBH, hΦH, hlb⟩
  · intro R _ t A' B' _ _ φA' φB' Φ' c hT hMat
    obtain ⟨g, hgt, hgc⟩ := GlobalTheory.T.exists_affineSpace_morphism_of_coordinates Rg (Sp R) (mA * mB) t
      (fun n => c (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2)
    have hgm : matOf g = c := by funext a b; simp [matOf, hgc]
    obtain ⟨hgen, hprop, hnorm⟩ := GlobalTheory.T.testHom_matrix_generates_normalised Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c hL hM
      hcov hαA hβB hT hMat
    rw [← hgm] at hgen hprop
    rw [← hgm, ← hgt] at hnorm
    have hP : IsPullback (φA' ≫ θ A) A'.hom (fA A) (g ≫ affπ Rg (mA * mB)) := by
      rw [hgt]; exact (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A _ _ _ _ t).1 hT.1.1
    have hbase : (Φ'.left ≫ φB' ≫ θ B) ≫ fA B = A'.hom ≫ g ≫ affπ Rg (mA * mB) := by
      rw [hgt, Category.assoc, Category.assoc, θf, hT.2.1.1.w, reassoc_of% (Over.w Φ')]
    have hforms := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ _ (fA A) (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (g ≫ affπ Rg _) (matOf g)
      hEmb hNB hNA hP.w hgen).2 ⟨_, hbase, hprop⟩
    obtain ⟨w₁, hw₁⟩ := (hW _ g).1 ⟨(hF _ _ g _ _ hP).1 hforms, (hNm _ g).1 hnorm, (hU _ _ g _ _ hP).1 hgen⟩
    have hA' : IsGrpPullback A' A ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φA' := by rw [hw₁, hgt]; exact hT.1
    have hB' : IsGrpPullback B' B ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φB' := by rw [hw₁, hgt]; exact hT.2.1
    obtain ⟨ψA', ψB', hψA', hψB', eψA', eψB', eΦ'⟩ := compare _ w₁ A' B' φA' φB' Φ' hA' hB'
      (by rw [hw₁]; exact hgen) (by rw [hw₁]; exact hprop)
    have hlb' := hT.2.2.2
    rw [← eψA', ← eψB'] at hlb'
    obtain ⟨w₂, hw₂⟩ := (hZ _ w₁ A' B' ψA' ψB' Φ' hψA' hψB' eΦ').1 hlb'
    refine ⟨w₂, ?_, ?_⟩
    · rw [Scheme.Hom.toImage_imageι_assoc, ← Category.assoc, ← Category.assoc, hw₂, hw₁, hgt]
    · rw [Scheme.Hom.toImage_imageι, ← Category.assoc, hw₂, hw₁, hgm]
  · intro R _ h A' B' _ _ φA' φB' Φ' hT hD
    obtain ⟨ψA', ψB', qA, qB, eA', eB', eΦ'⟩ := hD
    simp only [Scheme.Hom.toImage_imageι_assoc, Scheme.Hom.toImage_imageι] at hT ⊢
    have e₀ : A'.hom ≫ h = ψA' ≫ AH.hom := qA.1.w.symm
    have keyA : ψA' ≫ φAH ≫ θ A = φA' ≫ θ A := by rw [← eA', Category.assoc]
    have keyB : ψA' ≫ ΦH.left ≫ φBH ≫ θ B = Φ'.left ≫ φB' ≫ θ B := by
      rw [← eB']; simp only [Category.assoc]; rw [reassoc_of% eΦ']
    have hgen := hgH.comp ψA' h A'.hom e₀
    rw [keyA, ← matOf_comp] at hgen
    have hpr := hpH.comp ψA' h A'.hom e₀
    rw [keyA, keyB, ← matOf_comp] at hpr
    have hnorm : Normal ((h ≫ i ≫ j₁) ≫ affπ Rg (mA * mB)) (matOf (h ≫ i ≫ j₁)) αA βB :=
      (hNm _ _).2 ((hW _ _).2 ⟨h ≫ i, Category.assoc _ _ _⟩).2.1
    simp only [Category.assoc] at hT hnorm hgen hpr ⊢
    exact GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB R _ A' B' φA' φB' Φ' _ hL hM heA heB hcov hαA hβB hT
      hgen hpr hnorm

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingDetLineSectionOfHorizontal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.DetLine.FromGeneric GlobalTheory.ShFam.Hor.Sec

namespace GlobalTheory.DetLine.FromHorizontal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_renumber {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {m n : ℕ} (h : m = n)
    {x x' : Sp R ⟶ S} (hx : x = x') {v v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → v i = u k)
    (hu' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → v' i = u' k) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i, IsCombAtG t x v (M i) (v' i)) :
    ∃ M' : Matrix (Fin m) (Fin m) R, M'.det = M.det ∧ ∀ i, IsCombAtG t x' u (M' i) (u' i) := by
  subst h hx
  obtain rfl : v = u := funext fun i => hu i i rfl
  obtain rfl : v' = u' := funext fun i => hu' i i rfl
  exact ⟨M, rfl, hM⟩

theorem comb_left {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {n : ℕ} {a : Fin n → R}
    {u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} {z : epsAt x ⟶ t.G} (h : FramedFlatCoordinates.IsCombination x a u z) :
    IsCombAtG t x u a z.left :=
  have ⟨u', h₁, h₂⟩ := h
  ⟨u', h₁, congrArg CommaMorphism.left h₂.symm⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {V : Set (gen Y)} {τ : E →+* ℂ} {e : c.F →+* ℂ}

variable (Y V τ) in

abbrev Fr (R : Type) [CommRing R] : Type := Framed c Y.t (genι Y) (genStr Y) V τ D.p D.q R

def Agree {R : Type} [CommRing R] (f : Fr Y V τ R)
    (u : ∀ ρ : E →+* ℂ, Fin (D.mult ρ) → (Sp (DualNumber R) ⟶ Y.t.G.left)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (f.2.1 i).left = u τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (f.2.2.1 i).left = u (conjEmb τ) k

theorem exists_pullFr {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : Fr Y V τ R)
    {x' : Sp R' ⟶ gen Y} (hx : x' = spMap g ≫ b.1) :
    ∃ v w hf, factor g b (⟨x', v, w, hf⟩ : Fr Y V τ R') = 1 ∧
      ∀ u u', Agree b u → (∀ ρ i, u' ρ i = spMap (Chart.dualMapR g) ≫ u ρ i) →
        Agree (⟨x', v, w, hf⟩ : Fr Y V τ R') u' := by
  obtain ⟨j, h⟩ := b.2.2.2
  obtain ⟨v, w, h', a, a'⟩ := exists_pull g h hx
  refine ⟨v, w, ⟨_, h'⟩, ?_, fun u u' hu hu' => ⟨fun i k e => ?_, fun i k e => ?_⟩⟩
  · have h1 : IsChg Y.t (genι Y) g b.1 b.2.1 b.2.2.1 x' v w 1 1 := by
      refine ⟨hx, fun i => ?_, fun i => ?_⟩
      · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
      · simp only [← a']; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
    have := (factor_spec g b ⟨x', v, w, _, h'⟩ hx).2 1 1 h1
    rw [Matrix.det_one, Matrix.det_one, _root_.mul_one] at this
    exact this.symm
  · rw [hu', ← hu.1 i k e]; exact a i
  · rw [hu', ← hu.2 i k e]; exact a' i

theorem hor_factor (hτ : τ (H.rt : E) = H.rt0) {h : CxFr Y e → ℂ} (hh : HorFn τ h) {a a' : CxFr Y e} (hi : Inner a.1)
    (ha : a.1 = a'.1) {f f' : Fr Y V τ ℂ} (hf : f.1 = a.1.1) (hf' : f'.1 = a'.1.1) (hm : Agree f a.2.v)
    (hm' : Agree f' a'.2.v) : h a' = factor (RingHom.id ℂ) f f' * h a := by
  have hx : f'.1 = spMap (RingHom.id ℂ) ≫ f.1 := by rw [DetExtendZero.spMap_id, Category.id_comp, hf, hf', ha]
  obtain ⟨j, k⟩ := f.2.2.2
  obtain ⟨j', k'⟩ := f'.2.2.2
  obtain ⟨-, M, N, hc⟩ := exists_chg _ k k' hx
  have h1 := (factor_spec _ f f' hx).2 M N hc
  have h2 := (chg_isUnit k k' hc).1
  obtain ⟨-, hM, hN⟩ := hc
  simp only [DetExtendZero.dual_id, Category.id_comp] at hM hN
  obtain ⟨M', eM, hM'⟩ := exists_renumber (GlobalTheory.Harm.mult_of_mem D hτ) (congrArg (· ≫ genι Y) hf') hm.1 hm'.1
    fun i => comb_left (hM i)
  obtain ⟨N', eN, hN'⟩ := exists_renumber (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) (congrArg (· ≫ genι Y) hf') hm.2 hm'.2
    fun i => comb_left (hN i)
  have := hh.2.1 a a' M' N' hi ⟨ha, hM'⟩ ⟨ha, hN'⟩
  rw [eM, eN, h1] at this
  exact h2.mul_right_cancel (by rw [this]; ring)

theorem exists_section_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∃ σb : RuleY Y, SecY Y V τ σb ∧ NzY Y V τ σb := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hs hτ hh
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hs
  let sp (y : B.X) : Sp Γ(B.X, W y) ⟶ B.X := (hW y).fromSpec
  have hr {T : Scheme.{0}} (x : T ⟶ B.X) : Set.range (x ≫ io) ⊆ V := by
    rintro _ ⟨z, rfl⟩
    rw [← hV, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  choose bv bw hb hm using fun y =>
    (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) (sp y ≫ io) (hφ y) (hr _) (fr y)).1
  let b (y : B.X) : Fr Y V τ Γ(B.X, W y) := ⟨sp y ≫ io, bv y, bw y, _, hb y⟩
  let gm {U : B.X.Opens} {z : B.X} (hz : z ∈ U) : Γ(B.X, U) →+* B.X.presheaf.stalk z := (B.X.presheaf.germ U z hz).hom
  have hloc {y z : B.X} (hz : z ∈ W y) : locPt B.X z ≫ io = spMap (gm hz) ≫ (b y).1 := by
    rw [← Category.assoc]
    exact congrArg (· ≫ io) ((hW y).fromSpecStalk_eq_fromSpecStalk hz).symm
  choose ev ew he _ using fun z => exists_pullFr (gm (hy z)) (b z) (hloc (hy z))
  let fz (z : B.X) : Fr Y V τ (B.X.presheaf.stalk z) := ⟨locPt B.X z ≫ io, ev z, ew z, he z⟩
  have hgen (z : B.X) : genPt B.X ≫ io = spMap (algebraMap _ B.X.functionField) ≫ (fz z).1 := by
    rw [genPt_eq z, Category.assoc]
  obtain ⟨v₀, w₀, ⟨j₀, h₀⟩, -⟩ := exists_pullFr _ (fz (genericPoint B.X)) (hgen _)
  let a₀ : Fr Y V τ B.X.functionField := ⟨genPt B.X ≫ io, v₀, w₀, j₀, h₀⟩
  choose ε hε using fun z => (factor_spec _ (fz z) a₀ (hgen z)).1
  have hu {y z : B.X} (hz : z ∈ W y) : IsUnit (factor (gm hz) (b y) (fz z)) := (factor_spec _ _ _ (hloc hz)).1
  have hk (y : B.X) : a₀.1 = spMap (fnOf (W y) (gen_mem (hy y))) ≫ (b y).1 := hloc (gen_mem (hy y))
  choose δ hδ using fun y => (factor_spec _ (b y) a₀ (hk y)).1
  have hδε {y z : B.X} (hz : z ∈ W y) : (δ y : B.X.functionField) =
      ε z * algebraMap _ B.X.functionField (factor (gm hz) (b y) (fz z)) := by
    rw [hδ, hε, ← factor_comp _ _ _ _ _ (hloc hz) (hgen z)]
    congr 1
    exact (RingHom.ext fun r => algebraMap_germ hz r).symm
  have hg {y z : B.X} (hz : z ∈ W y) : germOf z (ε z)⁻¹ = germOf z (δ y)⁻¹ := by
    rw [germOf_eq_iff, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv, ← inv_div, hδε hz,
      mul_div_cancel_left₀ _ (ε z).ne_zero]
    exact UnitAt.inv ⟨_, hu hz, rfl⟩
  let Dv : B.Dv := show cartierGroup B.X from ⟨fun z => germOf z (ε z)⁻¹, fun y => ⟨W y, hy y, (δ y)⁻¹, fun z hz => hg hz⟩⟩
  have hD (y : B.X) (z : B.X) (hz : z ∈ W y) : Dv.IsEqn z (δ y)⁻¹ := hg hz
  obtain ⟨hne, hd⟩ := GlobalTheory.T.complexPoints_nonempty_dense_variety c.F B e
  have hA := hd (io ⁻¹ᵁ (genBd Y).compl) (by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      ⟨_, genericPoint B.X, rfl⟩
    exact ⟨z, fun hb => hb hz⟩)
  let R := AnRead.all B.str e B.dim
  choose u hu₁ he₁ using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y) hh.2.2.1 hh.2.2.2
  choose u' hu' he' using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  have h0 (y) (z) (hz : z ∈ ptsIn _ _ (io ⁻¹ᵁ (genBd Y).compl)) : h (a y z) ≠ 0 :=
    hh.1 _ ((inner_iff (ha y z)).2 hz)
  have htr (y y') (U : B.X.Opens) (r : Γ(B.X, U))
      (hr : ∀ hU, fnOf U hU r = (δ y' : B.X.functionField) / (δ y : B.X.functionField)) (p : CxPts B.str e)
      (h₁ : p ∈ ptsIn _ _ (W y)) (h₂ : p ∈ ptsIn _ _ (W y')) (h₃ : p ∈ ptsIn _ _ U)
      (hz : p ∈ ptsIn _ _ (io ⁻¹ᵁ (genBd Y).compl)) : h (a y p) = CxPts.ev _ _ U r p * h (a y' p) := by
    let z : B.X := p.1 (IsLocalRing.closedPoint ℂ)
    let χ : B.X.presheaf.stalk z →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) p.1).hom
    have hχ {U : B.X.Opens} (h : p ∈ ptsIn _ _ U) : χ.comp (gm (mem_ptsIn.1 h)) = evHom h :=
      (congrArg CommRingCat.Hom.hom (HolFrames.valR_eq_germ p.1 U h)).symm
    have hp : p.1 ≫ io = spMap χ ≫ (fz z).1 := by
      rw [← Category.assoc]
      exact congrArg (· ≫ io) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of ℂ) p.1).symm
    have hq {y : B.X} (h : p ∈ ptsIn _ _ (W y)) : p.1 ≫ io = spMap (evHom h) ≫ (b y).1 := by
      rw [← hχ, DetExtendZero.spMap_comp, Category.assoc, ← hloc, hp]
    obtain ⟨v, w, k, e₁, m⟩ := exists_pullFr _ (b y) (hq h₁)
    obtain ⟨v', w', k', e₂, m'⟩ := exists_pullFr _ (b y') (hq h₂)
    rw [hor_factor hτ hh ((inner_iff (ha y' p)).2 hz) (Subtype.ext ((ha y' p).trans (ha y p).symm))
      (f := ⟨_, v', w', k'⟩) (f' := ⟨_, v, w, k⟩) (ha y' p).symm (ha y p).symm
      (m' _ _ (hm y') (hv y' p h₂)) (m _ _ (hm y) (hv y p h₁))]
    congr 1
    have e₃ := factor_comp (evHom h₂) (RingHom.id ℂ) (b y') ⟨_, v', w', k'⟩ ⟨_, v, w, k⟩ (hq h₂)
      (by rw [DetExtendZero.spMap_id, Category.id_comp])
    rw [e₂, map_one, _root_.mul_one, RingHom.id_comp, ← hχ,
      factor_comp _ χ _ (fz z) ⟨_, v, w, k⟩ (hloc (mem_ptsIn.1 h₂)) hp] at e₃
    rw [← hχ, factor_comp _ χ _ (fz z) ⟨_, v, w, k⟩ (hloc (mem_ptsIn.1 h₁)) hp] at e₁
    have e₄ : factor (gm (mem_ptsIn.1 h₂)) (b y') (fz z) =
        factor (gm (mem_ptsIn.1 h₁)) (b y) (fz z) * gm (mem_ptsIn.1 h₃) r := by
      refine IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField (mul_left_cancel₀ (ε z).ne_zero ?_)
      rw [map_mul, ← _root_.mul_assoc, ← hδε, ← hδε]
      erw [algebraMap_germ]
      rw [hr, mul_div_cancel₀ _ (δ y).ne_zero]
    rw [← e₃, e₄, map_mul, ← _root_.mul_assoc, e₁, _root_.one_mul, ev_eq h₃, ← hχ]
    rfl
  obtain ⟨s, hs⟩ := exists_generates B Dv
    (GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot c.F B _ R _ (holSec_ne_bot hA _ W (fun y => (δ y)⁻¹) hy hD u hu₁
      (fun y z hz => by rw [he₁ y hz]; exact h0 y z hz.2) fun y y' r hr' z hz => by
        have hz' := mem_ptsIn_inf.1 hz.1
        rw [he₁ y ⟨hz'.1, hz.2⟩, he₁ y' ⟨hz'.2, hz.2⟩]
        exact htr y y' _ r (fun hU => by
          rw [hr', Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv]) z hz'.1 hz'.2 hz.1 hz.2))
    (GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot c.F B _ R _ (holSec_ne_bot hA _ W δ hy (fun y y' hy => inv_inv (δ y) ▸ (hD y y' hy).neg) u' hu'
      (fun y z hz => by rw [he' y hz]; exact inv_ne_zero (h0 y z hz.2)) fun y y' r hr' z hz => by
        have hz' := mem_ptsIn_inf.1 hz.1
        rw [he' y ⟨hz'.1, hz.2⟩, he' y' ⟨hz'.2, hz.2⟩]
        rw [eq_mul_inv_iff_mul_eq₀ (h0 y' z hz.2), htr y' y _ r hr' z hz'.2 hz'.1 hz.1 hz.2, _root_.mul_comm,
          mul_inv_cancel_right₀ (h0 y z hz.2)]))
  obtain ⟨σ, h1, h2, -⟩ := exists_section E H l c _ _ Y.t (genι Y) (genStr Y) τ D.p D.q B.X io V hio hV
    (hV ▸ frameCover_gen E H D l Xo c O β Y io.opensRange τ hτ) j₀ v₀ w₀ s h₀ fun z => by
      obtain ⟨j, hj⟩ := he z
      obtain ⟨-, M, N, hc⟩ := exists_chg _ hj h₀ (hgen z)
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (show Dv.IsEqn z (ε z)⁻¹ from rfl).generatesAt_iff.1 (hs z)
      refine ⟨j, ev z, ew z, M, N, t, hj, hc, ?_⟩
      rw [(factor_spec _ (fz z) a₀ (hgen z)).2 M N hc, ← hε, ht, Units.val_inv_eq_inv_val]
      have := (ε z).ne_zero
      field_simp
  exact ⟨σ, h1, h2⟩

end GlobalTheory.DetLine.FromHorizontal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionClosedFibreOfPrimitiveTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmDvr

theorem exists_unit_of_prim {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {J : Type}
    {c : J → FractionRing V} (b : FractionRing V) (hc : Prim (algebraMap V (FractionRing V)) c)
    (hb : Prim (algebraMap V (FractionRing V)) (fun j => b * c j)) :
    ∃ u : Vˣ, algebraMap V (FractionRing V) u = b := by
  obtain ⟨hc₁, j₀, hj₀, hj₀'⟩ := hc
  obtain ⟨hb₁, j₁, hj₁, hj₁'⟩ := hb
  have I1 : IsIntegral V b := by
    have := IsIntegral.mul (show IsIntegral V (b * c j₀) from hb₁ j₀) (show IsIntegral V (c j₀)⁻¹ from hj₀')
    rwa [_root_.mul_assoc, mul_inv_cancel₀ hj₀, _root_.mul_one] at this
  have hcne : c j₁ ≠ 0 := right_ne_zero_of_mul hj₁
  have I2 : IsIntegral V b⁻¹ := by
    have := IsIntegral.mul (show IsIntegral V (c j₁) from hc₁ j₁) (show IsIntegral V (b * c j₁)⁻¹ from hj₁')
    rwa [mul_inv, mul_left_comm, mul_inv_cancel₀ hcne, _root_.mul_one] at this
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 I1
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 I2
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hj₁
  have hvw : v * w = 1 := IsFractionRing.injective V (FractionRing V) (by
    rw [map_mul, hv, hw, mul_inv_cancel₀ hb0, map_one])
  exact ⟨⟨v, w, hvw, by rw [mul_comm, hvw]⟩, hv⟩

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    {g : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hp, hw⟩ := h
  have hN := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) hp t.PP.isLB P.isLB hN
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hN⟩ hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 P.isAb.proper,
    amplePt _ _ _ _ _ _ hφ _ _ P.isLB hN e P.ample P.ktriv⟩

end GlobalTheory.UMin.OmDvr

set_option maxHeartbeats 1000000 in
open GlobalTheory.UMin.OmDvr in

theorem GlobalTheory.UMin.exists_sec_nz_of_prim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  intro E _ _ _ H S t g m N V _ _ _ hV χ θ pt c hm h3 hu hP hT hc
  have hL := t.PP.isLB
  have : IsDiscreteValuationRing V := hV.1
  have := t.semi.comm
  have hpa := GlobalTheory.UMin.OmDvr.polAt_of_polFib t hP
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull χ t
  have hp' := GlobalTheory.SplitPoint.polAt_pullback m₁ hpa (jK V) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨σ₀, hσ₀⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H S t V χ _ m₁ hp'
  have h0V : spMap (RingHom.id V) ≫ χ = χ := (congrArg (· ≫ χ) (Spec.map_id _)).trans (Category.id_comp _)
  have hNZ := hσ₀ V (RingHom.id V) χ h0V
  obtain ⟨P, α, hg, hp, hw⟩ := hP
  have hx0 : spMap (RingHom.id (FractionRing V)) ≫ (spMap (algebraMap V (FractionRing V)) ≫ χ) =
      spMap (algebraMap V (FractionRing V)) ≫ χ :=
    (congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp (FractionRing V)) t.G t.PP.L hL P _ α hp hw
    (FractionRing V) (𝟙 _) _ (Category.id_comp _)
  obtain ⟨a, ha⟩ := he.ex (RingHom.id _) hx0 (SecM.ofSec t.G θ)
  generalize VVRank.pullS t.G _ (Over.homMk (spMap (RingHom.id V)) h0V : Over.mk χ ⟶ Over.mk χ) σ₀ = σ₁ at hNZ
  obtain ⟨s, hs⟩ := he.ex (RingHom.id _) hx0 (pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁))
  have hmK : ((m : ℕ) : FractionRing V) ≠ 0 := by
    have := (hu.map (algebraMap V (FractionRing V))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨j₀, hj₀, -⟩ := hc.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h00 : SecM.ofSec t.G θ = @id Γ((Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ)).left, ⊤)
        (GlobalTheory.ZH.fn (0 : FractionRing V)) • SecM.ofSec t.G θ := by
      change _ = fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) 0 • _
      rw [map_zero, zero_smul, ha, map_zero, zero_smul]
    have q := (GlobalTheory.UMin.thG_smul_iff S t.G t.PP.L t.PP.rig hL t.PP.rigGen g m (FractionRing V) _ θ θ (pt j₀) 0 (c j₀) (c j₀) hm
      hmK ⟨P, α, hg, hp, hw⟩ h00 (hT.2.1 j₀)).1 (hT.2.1 j₀)
    exact hj₀ (by simpa using q)

  have hrel : pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁) =
      fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) (s * a⁻¹) • SecM.ofSec t.G θ := by
    have key : s = (s * a⁻¹) * a := by rw [_root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]
    rw [hs, ha, smul_smul, ← map_mul, ← key]
  have hT' : ThList t.G t.PP.L t.PP.rig m (spMap (algebraMap V (FractionRing V)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ₁ (algebraMap V (FractionRing V))) pt (fun j => (s * a⁻¹) * c j) := by
    refine ⟨hT.1, fun j => ?_, hT.2.2⟩
    show ThG t.G t.PP.L t.PP.rig m _ (pt j) (fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) ((s * a⁻¹) * c j))
    rw [map_mul]
    exact ThG.smul hL hrel (hT.2.1 j)
  have hprim := GlobalTheory.UMin.prim_of_polFib E H S t g V hV χ ⟨P, α, hg, hp, hw⟩ _ hNZ m N hm h3 hu (FractionRing V)
    (algebraMap V (FractionRing V)) pt _ (IsFractionRing.injective V (FractionRing V)) hT'
  obtain ⟨u, hu'⟩ := exists_unit_of_prim (s * a⁻¹) hc hprim
  have hpull : pl (algebraMap V (FractionRing V)) rfl (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁) = SecM.ofSec t.G θ := by
    rw [pl_smul, hrel, smul_smul, ← map_mul, ← hu', ← map_mul, Units.inv_mul, map_one, map_one, one_smul]
  refine ⟨SecM.toSec t.G (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁), hpull, ?_⟩
  obtain ⟨g₀, h₁, h₂⟩ := hNZ
  refine ⟨g₀, h₁, ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₂
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  change g₀ ∈ Scheme.basicOpen _ (liftHom t.G _ (fnR χ (u⁻¹ : Vˣ).val) * σ₁.f k)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (((u⁻¹).isUnit.map (fnR χ)).map (liftHom t.G _))]
  exact ⟨Scheme.basicOpen_le _ _ hk, hk⟩
end
end

