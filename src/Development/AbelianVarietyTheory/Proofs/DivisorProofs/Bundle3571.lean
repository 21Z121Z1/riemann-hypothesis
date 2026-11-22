import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3560
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEqOfCodimOneEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelOne

variable {R : Type} [CommRing R]

theorem pull_iso_bijective' {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar B) = laurentVar C := by
  ext
  simp only [laurentVar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have h := congrArg (fun g => g.hom (LaurentPolynomial.T 1 : LaurentPolynomial B))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [laurentMap_T] at h
  exact h.symm

end GlobalTheory.EtC.GmStep.LevelOne

namespace GlobalTheory.EtC.GmStep.LevelOne

theorem rowOne_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (rowOne A A' q i k) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, h2⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr1 := GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap1 := congrArg (fun f => disc.map f) h1
  have hmap2 := congrArg (fun f => disc.map f) h2
  simp only [Functor.map_comp] at hmap1 hmap2
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.comp
      (LaurentPolynomial.C : A →+* LaurentPolynomial A))
    simpa using this
  have hkum : pull _ (disc.map e.hom) (tw q 1) 1 (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A))) =
      kum q (laurentVar (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) := by
    rw [← pull_comp, augK]
    erw [hmap2]
    have := (GlobalTheory.EtC.a6nat_holds q).2.2.2 (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A
      (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) (laurentVar A) hqL
    rw [laurentVar_map] at this
    exact this
  have hcst : ∀ a, pull _ (disc.map e.hom) (tw q (i - 1)) 0
      (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q (i - 1)) 0
        (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    rw [← pull_comp, hmap1, pull_comp]
    rfl
  have heq : ∀ a, pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1 (rowOne A A' q i k a) =
      gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    simp only [rowOne, gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [pull_cast, (GlobalTheory.EtC.a6nat_holds q).1, hcst, hkum]
    rfl
  have hcomp : (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) ∘ (rowOne A A' q i k) =
      (gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i) ∘ (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) :=
    pull_iso_bijective' (disc.mapIso e) (tw q i) 1
  have he0 : Function.Bijective (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    pull_iso_bijective' (disc.mapIso e0) (tw q (i - 1)) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr1.comp he0

end GlobalTheory.EtC.GmStep.LevelOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsBoundOfDeepGood
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

namespace GlobalTheory.CovTop.DescentMaps

theorem mapsCore {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {D : D7} {x : ℝ}
    {V : (c.F →+* ℂ) → HSp D} {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
    (S : Subgroup (LevelAut Dw l)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Gm W G : WTZ E) (hGW : Gm + W = G)
    (hGm : Even Gm.2) (hW : Even W.2) (hKG : KeepsCusp U G) (hKW : KeepsCusp U W)
    (hLG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U G → g ∈ latW U G)
    (hLW : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W)
    (hNG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict G σ g = GlobalTheory.AllWt.normW U x V dict G σ f)
    (hGood : GoodW U x V dict G) (hGoodP : GoodW U x V dict (G + W))
    (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (hu : u ∈ latW U W)
    (hdet : ∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (γ : LevelAut Dw l) (f : cuspW Xo c U Gm) (g : cuspW Xo c U (Gm + W)), (g : Rul Xo c) = f * pull Xo c γ u →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict Gm σ f)
    (b : ℝ) (hb : (Fintype.card S : ℝ) ^ 3 * B ^ 2 ≤ Real.exp (2 * b))
    (Lt : Submodule (𝓞 c.F) (cuspW Xo c U G)) (hLt : Lt = GlobalTheory.LevDesc.chiLat S U G χ) (Gp : WTZ E) (hGp : G + W = Gp) :
    ∃ (n : ℕ) (φ : Fin n → cuspW Xo c U Gm →ₗ[c.F] cuspW Xo c U G),
      (∀ h, ∀ f ∈ latW U Gm, φ h f ∈ Lt) ∧ (∀ f, (∀ h, φ h f = 0) → f = 0) ∧
      (∀ σ f, ∑ h, GlobalTheory.AllWt.normW U x V dict G σ (φ h f) ^ 2 ≤
        Real.exp (2 * b) * GlobalTheory.AllWt.normW U x V dict Gm σ f ^ 2) ∧
      n * Formalism.HN.rkK Lt ≤ rankW U Gp := by
  subst hGW hLt hGp
  have hm : ∀ f ∈ cuspW Xo c U Gm, ∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ (u : Rul Xo c) f h ∈ cuspW Xo c U (Gm + W) :=
    fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hGm hW hKG hKW χ u.2 hf h
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun k => LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm, ?_, ?_, ?_, ?_⟩
  · intro k f hf
    exact GlobalTheory.LevDesc.cuspPh_mem_chiLat Xo c U S hpq hA Gm W hGm hW hKG hKW hLG hLW χ u hu f hf (e k)
  · intro f hf0
    have hsec : (f : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ f.2)
    have husec : (u : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ u.2)
    apply Subtype.ext
    refine GlobalTheory.levPh_injective_of_levDet_nonZeroDivisor Xo c S hpq hA χ u husec hdet _ hsec fun h => ?_
    have h1 := hf0 (e.symm h)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Equiv.apply_symm_apply] at h1
    rw [← GlobalTheory.LevDesc.coe_cuspPh S χ _ hm f h, h1]
    rfl
  · intro σ f
    have h1 : ∑ k, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ ((LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm) f) ^ 2 =
        ∑ h : S, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2 :=
      e.sum_comp (fun h : S => GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2)
    rw [h1]
    refine (GlobalTheory.sum_sq_normW_cuspPh_le Xo c U x V dict S hpq hA Gm W hGm hW hKG hKW χ u B hB0 hGood.1 hNG hB f σ).trans ?_
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  · exact GlobalTheory.CovolRank.card_mul_rkK_chiLat_le_rankW Xo c U x V dict S hpq hA (Gm + W) W (hGm.add hW) hW hKG hKW hGood hGoodP χ u hdet

end GlobalTheory.CovTop.DescentMaps

namespace GlobalTheory.CovTop.DescentMaps

set_option maxHeartbeats 1000000 in

theorem maps : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Gram → DeepGood → Size → FlatDeg → Maps := by
  intro hP hGD hQ hSI hTF hSN hGram hDG hSz hFD
  obtain ⟨C, hC0, hub⟩ := GlobalTheory.T.exists_uniform_height_constant hP hGD hQ hSI hTF hSN
  have hT := GlobalTheory.T.lattice_level_character_bound hP hGram hDG
  have hS := GlobalTheory.T.size_bounds_for_family hSz
  have hH := GlobalTheory.CovTop.Sizes.hostN (2 * C + 200)
  unfold Maps Covers Lifts
  unfold DeepGood at hDG
  unfold FlatDeg at hFD
  unfold Covers Lifts at hT hS hDG hFD
  unfold HostN Lifts at hH
  refine Closed.imp ((((hT.and hS).and hH).and hDG).and hFD) ?_
  intro eps Fm CH _ hall0
  obtain ⟨⟨⟨⟨⟨C1, -, hT'⟩, ⟨C2, -, hS'⟩⟩, ⟨A, -, hH'⟩⟩, ⟨C4, -, hDG'⟩⟩, ⟨C5, -, hFD'⟩⟩ := hall0
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hall⟩ := (((hT'.and hS').and hH').and hDG').and hFD'
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hall x hx hle ι p hp
  obtain ⟨fr, ψ, -, hl, hlat, hcard⟩ := a1 i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hE, hfr, hexp, hg, hf8, hr100, hflat, -⟩ := a2 i hi Y hY
  have hN := a3 i
  have hDGY := a4 i hi Y hY
  have hFDY := a5 i hi Y hY

  obtain ⟨-, hpq, hq, h2q⟩ := GlobalTheory.Member.exists_iotaOK (Fm.D x ι) p.T.Q hLaws.pins ((i : ℕ) + 1) hInR
  have hq1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [hq]; simp only [Formalism.MainNotions.WeightFamilies.rho, Formalism.BasicNotions.Ranks.sigW]; omega
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by omega
  have hfin : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by rw [hN.deg]; omega

  obtain ⟨u, hu, hdet, hB⟩ := hub (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 (Fm.L x ι).sc.L hL1
    hM hE hfr (le_of_eq rfl) _ hFDY (by rw [abs_neg]; exact hflat) hexp hg hf8 hr100 fr
  have hK := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1

  have hGk : Even (Gk p i).2 := (p.κ i).n_even.natCast
  have hW : Even (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0).2 :=
    GlobalTheory.AllWt.even_wtOf _ _
  have hGm : Even (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))).2 := hGk.add (GlobalTheory.AllWt.even_wtOf _ _)
  have hGW : Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 = Gk p i := by
    simp only [Gs, shiftG, add_assoc, ← GlobalTheory.AllWt.wtOf_add, neg_smul, neg_add_cancel, add_zero, GlobalTheory.AllWt.wtOf_zero]

  set z := zBase (Fm.L x ι) with hz
  have hzL : (Fm.L x ι).sc.L ≤ z := by
    have h8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have h100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have h0 : (0 : ℝ) ≤ (Fm.L x ι).sc.L := by linarith
    rw [hz, zBase]
    nlinarith [mul_le_mul h8 h100 (by norm_num) (by linarith)]
  have hz1 : 2 * C + 200 ≤ z := hN.big.1.trans hzL
  have hPP : z ^ 12 ≤ (Fm.L x ι).sc.b := by
    have h1 := hN.ppLow
    obtain ⟨hA1, hA2, -⟩ := hN.poly
    have h3 := hN.room
    have hz0 : 1 ≤ z := by linarith
    have hx1 : 1 ≤ (Fm.L x ι).sc.x ^ A := le_trans (one_le_pow₀ hz0) (h1.trans hA2)
    have h4 : (Fm.L x ι).sc.x ^ A ≤ ((Fm.L x ι).sc.x ^ A) ^ (2 * C + 200) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) ≤ 2 * C + 200 by linarith)
    linarith
  have hb : (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (C * ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 9) ^ 2 ≤
      Real.exp (2 * (Fm.L x ι).sc.b) := by
    have hz9 : ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L : ℝ) = z := by rw [hz, zBase]
    rw [hz9]
    rw [Nat.card_eq_fintype_card] at hcard
    have hn0 : (0 : ℝ) < Fintype.card (grpHR fr) := by exact_mod_cast Fintype.card_pos
    have hz0 : 1 ≤ z := by linarith
    have hn3 : (Fintype.card (grpHR fr) : ℝ) ^ 3 ≤ Real.exp (135 * z ^ 2) := by
      rw [← Real.exp_log (pow_pos hn0 3), Real.log_pow]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have he : Real.exp (C * z ^ 9) ^ 2 = Real.exp (2 * C * z ^ 9) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [he]
    calc (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (2 * C * z ^ 9)
        ≤ Real.exp (135 * z ^ 2) * Real.exp (2 * C * z ^ 9) :=
          mul_le_mul_of_nonneg_right hn3 (Real.exp_pos _).le
      _ = Real.exp (135 * z ^ 2 + 2 * C * z ^ 9) := by rw [← Real.exp_add]
      _ ≤ Real.exp (2 * (Fm.L x ι).sc.b) := by
          refine Real.exp_le_exp.2 ?_
          have a1 : z ^ 2 ≤ z ^ 9 := pow_le_pow_right₀ hz0 (by norm_num)
          have a2 : z ^ 10 ≤ z ^ 12 := pow_le_pow_right₀ hz0 (by norm_num)
          have a3 : (135 + 2 * C) * z ^ 9 ≤ z * z ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have a4 : z * z ^ 9 = z ^ 10 := by ring
          nlinarith

  have e2 : Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1)) = Gk p i +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 := by
    unfold Gs Gk shiftG; rfl
  obtain ⟨n, φ, h1, h2, h3, h4⟩ := mapsCore (grpHR fr) (Nat.le_add_right_of_le hp1) hl.coprime
    (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))))
    (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0) (Gk p i) hGW
    hGm hW (hK _ hGk).1 (hK _ hW).1 (fun γ f g hg => ((hK _ hGk).2 γ f g hg).1)
    (fun γ f g hg => ((hK _ hW).2 γ f g hg).1) (fun γ f g hg => ((hK _ hGk).2 γ f g hg).2)
    hDGY.1 hDGY.2.2.1 (GlobalTheory.LevDesc.chiHR fr ψ) u hu hdet _ (Real.exp_pos _).le
    (fun γ f g hg σ => hB γ _ f g hGm hg σ) _ hb (latDeep p i Y) hlat
    (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1))) e2.symm
  exact ⟨n, φ, h1, h2, h3, h4⟩

end GlobalTheory.CovTop.DescentMaps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairingStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ y : HdR B, (∀ x ∈ Fil A, φ x y = 0) → y ∈ Fil B := by
  first | exact @GlobalTheory.PoincareKer.mem_fil_of_orth | exact GlobalTheory.PoincareKer.mem_fil_of_orth | (intros; apply GlobalTheory.PoincareKer.mem_fil_of_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegMinTop

theorem lemProper : ∀ (R o' : Type) [CommRing R] [IsNoetherianRing R] [CommRing o'] (β : R →+* o') (S' X Z : Scheme.{0}) (s' : S' ⟶ Sp o') (z : Z ⟶ Sp R) (π : S' ⟶ Z) (i : X ⟶ Z) (U : S'.Opens) (c : U.toScheme ⟶ X), IsProjOver s' → β.Finite → IsProjOver z → Surjective c → U.ι ≫ π = c ≫ i → Dense (Set.range i) → π ≫ z = s' ≫ spMap β → Surjective π ∧ IsProper π ∧ AlgebraicGeometry.IsNoetherian Z := by
  intro R o' _ _ _ β S' X Z s' z π i U c hs' hβ hz hc hUπ hi hπz
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hs'
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hz
  haveI : IsFinite (spMap β) := (IsFinite.SpecMap_iff _).2 hβ
  haveI : IsProper (π ≫ z) := by rw [hπz]; infer_instance
  haveI : IsProper π := IsProper.of_comp π z
  refine ⟨⟨?_⟩, inferInstance, ?_⟩
  · have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hsub : Set.range i ⊆ Set.range π := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := c.surjective x
      exact ⟨U.ι u, by rw [← Scheme.Hom.comp_apply, hUπ, Scheme.Hom.comp_apply]⟩
    have h := hi.closure_eq ▸ closure_minimal hsub hcl
    exact fun y => h (Set.mem_univ y)
  · have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace z
    exact {}

theorem lemGen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens) [Nonempty U], ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt ∧ Set.range x = {genericPoint U.toScheme} := by
  intro o Ω _ _ _ M U _
  obtain ⟨⟨y₀, hy₀⟩⟩ := ‹Nonempty U›
  have hsub : Set.range M.pt ⊆ Set.range U.ι := by
    rw [M.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_specializes y₀).mem_open U.isOpen hy₀
  have hg : U.ι (genericPoint U.toScheme) = genericPoint M.Z := by
    have h1 := (genericPoint_spec U.toScheme).image U.ι.continuous
    rw [Set.image_univ, Scheme.Opens.range_ι, (U.isOpen.dense ⟨y₀, hy₀⟩).closure_eq] at h1
    exact h1.eq (genericPoint_spec M.Z)
  set x := IsOpenImmersion.lift U.ι M.pt hsub with hx
  have hxU : x ≫ U.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxa : ∀ a, x a = genericPoint U.toScheme := fun a => by
    apply U.ι.isOpenEmbedding.injective
    rw [hg, ← M.pt_apply a, ← hxU, Scheme.Hom.comp_apply]
  refine ⟨x, hxU, Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint Ω, hxa _⟩, ?_⟩⟩
  rintro _ ⟨a, rfl⟩
  exact hxa a

theorem minSt5 : GlobalTheory.SiegJoin.MinSt5 := by
  intro g hg n hn ho F
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hℓo : Odd ℓ := Odd.of_dvd_nat ho hℓn
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨hXi, hXn, -⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn ho F
  obtain ⟨P, rig, hPg, hPs, hrig, -⟩ := GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli g n hg hn ho F W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.siegelThetaMap_deepLevel_finite_fibres ℓ hℓ hℓo g
  have hmo : Odd (ℓ ^ (j₀ + 1)) := hℓo.pow
  have hm3 : 3 ≤ ℓ ^ (j₀ + 1) := by
    have h2 := hℓ.two_le
    have h1 : ℓ ≤ ℓ ^ (j₀ + 1) := Nat.le_self_pow (by omega) ℓ
    obtain ⟨k, hk⟩ := hℓo
    omega
  have hmu : IsUnit ((ℓ ^ (j₀ + 1) : ℕ) : cycAway n) := by
    obtain ⟨k, hk⟩ := hℓn
    have hu := isUnit_natCast (n := n) (by omega)
    have e : ((n : ℕ) : cycAway n) = (ℓ : cycAway n) * (k : cycAway n) := by
      rw [← Nat.cast_mul, ← hk]
    rw [e] at hu
    rw [Nat.cast_pow]
    exact (isUnit_of_mul_isUnit_left hu).pow _
  obtain ⟨N, f, hf⟩ := GlobalTheory.T.exists_thetaMap_eighthPower_siegelModuli g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) hPg hPs hrig hmo hm3 hmu
  have hq : QFin f := hj₀ (j₀ + 1) (by omega) n hg hn ho F W hW hℓn P rig N f hf
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hf.2.2.2.2.2.2.2.1
  have hlft : LocallyOfFiniteType F.s := GlobalTheory.SiegUnram.locallyOfFiniteType_of_isQProjOver F.qproj
  have hqc : QuasiCompact F.s := GlobalTheory.SiegelFamilyBaseChange.quasiCompact_of_isQProjOver F.qproj
  obtain ⟨Z, p, i, hpf, hio, hip, hZn, hZi, hid⟩ :=
    GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite (cycAway n) N F.X F.s f hXi hXn hlft hqc F.isSeparated hfs hq
  obtain ⟨hzproj, hOZlb, hOZamp, -⟩ := GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist (cycAway n) N 8 Z p (by norm_num) hpf
  obtain ⟨o, Ω, _, _, _, _, β, S, ρ, u, Y, q, hsys, hlev, hbig, hfin⟩ :=
    GlobalTheory.T.exists_realisedThetaSystem_normalLevelModel ℓ hℓ hℓo j₀ g n hg hn ho F W hW hℓn (hbas g)
  obtain ⟨X, M, U₀, EE, fM, Xab, Zh, hmin, hab, habeq⟩ := GlobalTheory.T.exists_normal_projective_toric_minor_model o Ω S ρ hbig hfin
  have hXnm : X.IsNm S.th := hmin.1
  have hXnorm : Geo.Tor.IsNormalScheme X.Z := hmin.2.2.1
  have hover : S.Over₀ M U₀ := hmin.2.2.2.1
  obtain ⟨d, hd, hdo⟩ :=
    GlobalTheory.T.levelCover_openImmersion_normalisedThetaClosure g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys hq Y X q hlev hXnm hXnorm
  obtain ⟨U, c, hUc, -⟩ :=
    GlobalTheory.T.level_cover_image_open_finite_over_moduli g n hg hn ho F W hW o Ω β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin habeq hd hdo
  obtain ⟨G, _, e, _, hGs, hGsm, hGpb, hGh⟩ :=
    GlobalTheory.T.eighth_power_first_factor_theta_model g n hg hn ho F W hW o Ω β S ρ u hsys M U₀ EE Zh U c hover hUc
  obtain ⟨eS, hSymE, hcrd⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys
  have hMn : Geo.Tor.IsNormalScheme M.Z := hover.normal
  have hscale := GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys M eS hMn
    hover.div hSymE
  have hediv : M.HasDiv eS := fun z' => by
    obtain ⟨i', hi'⟩ := hover.div z'
    obtain ⟨j', hj', -⟩ := hscale z' i' hi'
    exact ⟨j', hj'⟩
  obtain ⟨h, hhs, hhc⟩ := GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β M N eS hediv
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  obtain ⟨δ, t, hδ, htop, -, hsec⟩ := GlobalTheory.TupleBundle.exists_lb_of_hasDiv o Ω M S.Gam S.th hover.div
  have hhb := GlobalTheory.T.pull_O1_section_coordinates_power o Ω (cycAway n) M S.Gam S.th δ t N (N + 1).factorial eS h hδ htop hsec hhc hscale
  have hSg : S.g = 8 * g := hsys.2.2.1
  have hkey := GlobalTheory.T.thetaConstantBundle_pow_eight_iso_detHodge_pow_four o Ω S ρ M U₀ EE Zh (by omega) hover hab δ t hδ htop hsec
  haveI : Nonempty U := ⟨⟨_, hUc.1.some_mem⟩⟩
  obtain ⟨x, hxU, hxg⟩ := lemGen o Ω M U
  have hUh : U.ι ≫ h = c ≫ f := GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N U.toScheme (c ≫ F.s) (U.ι ≫ h) (c ≫ f) Ω x eS
    (by rw [Category.assoc, hhs, hUc.2.2.2.1]) (by rw [Category.assoc, hfs]) hxg
    (by rw [← Category.assoc, hxU]; exact hhc)
    (by rw [← Category.assoc, hUc.2.2.2.2 x hxU, Category.assoc]; exact hcrd _ rfl)
  haveI : Surjective c := hUc.2.2.1
  have hUd : Dense (U : Set M.Z) := U.isOpen.dense hUc.1
  obtain ⟨π, hπU, hπp⟩ := GlobalTheory.T.normal_scheme_extension_through_finite_cover (cycAway n) N M.Z F.X Z U c i p h inferInstance hMn hZi hUd
    inferInstance hpf hio hid (by rw [hUh, hip])
  have hss : π ≫ p ≫ PSpace.str (cycAway n) N = M.s ≫ spMap β := by rw [← Category.assoc, hπp, hhs]
  obtain ⟨hπs, hπpr, hZno⟩ := lemProper (cycAway n) o β M.Z F.X Z M.s (p ≫ PSpace.str (cycAway n) N) π i U c
    hover.proj hsys.1 hzproj hUc.2.2.1 hπU hid hss
  have hTI : GlobalTheory.Poinc.ThetaInt F W i := by
    have h0 := GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf
    rw [← hip] at h0
    intro o' Ω' _ _ _ _ S' ρ' u' hsh hgen M' π' hM' hpt
    exact h0 o' Ω' S' ρ' u' hsh hgen M' (π' ≫ p) hM' (by rw [← Category.assoc, hpt]; simp only [Category.assoc])
  have hiz : i ≫ p ≫ PSpace.str (cycAway n) N = F.s := by rw [← Category.assoc, hip, hfs]

  haveI : IsSeparated G.hom := hGs.separated
  haveI : IsSeparated Zh.G.hom := Zh.semi.separated
  haveI := hGsm
  haveI := Zh.dim
  have hH2 : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega G g).isLB_det
  have hH1 : (hodge Zh.G S.g).IsLB := (GlobalTheory.LieVB.isVB_omega Zh.G S.g).isLB_det
  have hO := GlobalTheory.ProjSpace.O1_isLB (cycAway n) N
  have hLB : LBIso ((lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8).pull π)
      (lbPow (hodge G g) (32 * (N + 1).factorial)) := by
    have e1 := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hO h) (isLB_lbPow hδ _)).2 hhb
    have e2 := (GlobalTheory.CechPic.cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hH1 4)).2 hkey
    have e3 := (GlobalTheory.CechPic.cls_eq_iff hH1 (isLB_lbPow hH2 8)).2 hGh
    rw [GlobalTheory.CechPic.cls_pull hO, GlobalTheory.CechPic.cls_lbPow hδ] at e1
    rw [GlobalTheory.CechPic.cls_lbPow hδ, GlobalTheory.CechPic.cls_lbPow hH1] at e2
    rw [GlobalTheory.CechPic.cls_lbPow hH2] at e3
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hOZlb π) (isLB_lbPow hH2 _)).1 ?_
    rw [GlobalTheory.CechPic.cls_pull hOZlb, GlobalTheory.CechPic.cls_lbPow (pull_isLB hO p), GlobalTheory.CechPic.cls_pull hO,
      GlobalTheory.CechPic.cls_lbPow hH2, map_nsmul, ← GlobalTheory.CechPic.pull_comp, hπp, e1, smul_comm 8, e2, e3, smul_smul,
      smul_smul]
    congr 1
    ring
  refine ⟨Z, p ≫ PSpace.str (cycAway n) N, i, lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8, o, inferInstance, β,
    M.Z, M.s, U, c, π, G, inferInstance, e, inferInstance, 32 * (N + 1).factorial,
    ⟨⟨hzproj, GlobalTheory.IsNormalScheme.of_pred hZn, hio, hiz, hid, W, hW, hTI⟩, hzproj, GlobalTheory.IsNormalScheme.of_pred hZn,
      hiz, hid, hOZlb, hOZamp⟩,
    ⟨hsys.1, hsys.2.1, hover.proj, GlobalTheory.IsNormalScheme.of_pred hMn, hUd, hUc.2.1, hUc.2.2.1, hπU, hss, hπs, hπpr, hZno⟩,
    ⟨hGs, hGsm, hGpb⟩, by have := Nat.factorial_pos (N + 1); omega, hLB⟩

end GlobalTheory.SiegMinTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_descends_of_closedFibre_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  first | exact @GlobalTheory.Mum.descend_of_emb | exact GlobalTheory.Mum.descend_of_emb | (intros; apply GlobalTheory.Mum.descend_of_emb <;> assumption)
end

