import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingThird
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.LevKProof

variable {D : D7}

theorem blkOf_zero_of_le {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem secondBlockIndex_eq_zero_of_dim_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_singleBlock_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [secondBlockIndex_eq_zero_of_dim_le h] at hik
  exact absurd hik (lt_irrefl _)

end GlobalTheory.SeriesTie.LevKProof

namespace GlobalTheory.SeriesTie

open LevKProof in

theorem levK_eq_levG_triv : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hp i j b
  unfold Setup.levK levG
  rw [hp.frT]
  congr 1
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (flag1L (ρ.B i j b).G.levT) =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    unfold parLev
    have hP : (flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hp.Pg i j b
    have hb : (blkOf (flag1L (ρ.B i j b).G.levT).r (flag1L (ρ.B i j b).G.levT).t : Fin (Wc D j).rank → ℕ) =
        blkOf (Rl.datWp j Rl.triv).r (Rl.datWp j Rl.triv).t :=
      (blkOf_zero_of_le le_rfl).trans (blkOf_zero_of_le hr).symm
    have hb2 : (blk2 (flag1L (ρ.B i j b).G.levT).r : Fin (Wc D j).rank → ℕ) = blk2 (Rl.datWp j Rl.triv).r :=
      (secondBlockIndex_eq_zero_of_dim_le le_rfl).trans (secondBlockIndex_eq_zero_of_dim_le hr).symm
    rw [hP, hb, hb2]
    rfl
  have h1 : (flag1L (ρ.B i j b).G.levT).P.H = ⊥ := rfl
  have h2 : (Rl.datWp j Rl.triv).P.H = ⊥ := rfl

  have key : ∀ (x : GL (Fin (Wc D j).rank) (Lev.EAf D)) (PP : Pl D.host.E) (e1 : PP ∈ (flag1L (ρ.B i j b).G.levT).Pg)
      (e2 : PP ∈ (Rl.datWp j Rl.triv).Pg) (a c : Fin (Wc D j).rank),
      (rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x ⟨PP, e1⟩).val a c =
        (rTup (Rl.βW j) (Rl.datWp j Rl.triv) x ⟨PP, e2⟩).val
          (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) := by
    intro x PP e1 e2 a c
    unfold rTup
    erw [upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le le_rfl _)]
    rfl
  have hiff : ∀ x : GL (Fin (Wc D j).rank) (Lev.EAf D),
      rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x = 1 ↔ rTup (Rl.βW j) (Rl.datWp j Rl.triv) x = 1 := by
    intro x
    constructor
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e1 : PP.1 ∈ (flag1L (ρ.B i j b).G.levT).Pg := by
        show PP.1 ∈ (ρ.B i j b).G.Pg
        rw [hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 e1 PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
      rw [h] at hk
      refine hk.symm.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      erw [Matrix.one_apply]
      simp [Fin.ext_iff]
      rfl
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e2 : PP.1 ∈ (Rl.datWp j Rl.triv).Pg := by
        show PP.1 ∈ Rl.Pg
        rw [← hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 PP.2 e2 a c
      rw [h] at hk
      refine hk.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      rfl
  ext x
  change (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _) ↔ (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _)
  rw [hpar, h1, h2, Subgroup.mem_bot, Subgroup.mem_bot, hiff]

end GlobalTheory.SeriesTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatible
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcDepth

theorem eq_pow_natDegree_of_dvd {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hd : p ∣ (X - 1) ^ n) :
    p = (X - 1) ^ p.natDegree := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at hd ⊢
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) n).1 hd
  have hpi := eq_of_monic_of_associated hp ((monic_X_sub_C (1 : ℂ)).pow i) hi
  rw [hpi, natDegree_pow, natDegree_X_sub_C, mul_one]

theorem prod_map_pow {α : Type*} (q : ℂ[X]) (f : α → ℕ) (s : Multiset α) :
    (s.map fun y => q ^ f y).prod = q ^ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, pow_add]

theorem fixed_ne_bot_iff_isTameWD : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
      ∀ x : IrrGL (w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  intro hDZC hDZI hEx hZel hGeo hBZ E Ω _ _ _ _ _ A w h rc hrc x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨a, ha, ε, -, hL⟩ := id hrc
  obtain ⟨m, hm⟩ := hEx _ x
  have hs : HasSupport x.rep (msupp m) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZel _ m x hm
  have hcp := GlobalTheory.T.central_character_rec_compatible hEx hZel hGeo hBZ E Ω A w h a ha _ rc hL x (msupp m) hs
  have hdy : ∀ y ∈ msupp m, (fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ ↔ IsTameWD (rc y)) :=
    fun y hy => hDZC E Ω A w h rc hrc y (hs.isCusp hy)
  have htame : IsTameWD (rc x) ↔ ∀ y ∈ msupp m, IsTameWD (rc y) := by
    simp only [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly E Ω A w h]
    constructor
    · intro H y hy σ hσ
      have hdvd : (rc y).charPol σ ∣ (rc x).charPol σ := by
        rw [hcp σ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
      rw [H σ hσ] at hdvd
      have e := eq_pow_natDegree_of_dvd ((rc y).charPol_monic σ) hdvd
      rwa [WD.charPol_natDegree] at e
    · intro H σ hσ
      rw [hcp σ, Multiset.map_congr rfl (fun y hy => H y hy σ hσ), prod_map_pow]
      congr 1
      rw [hL.dim x, Multiset.map_congr rfl (fun y _ => hL.dim y), hs.sum_fst, Fintype.card_fin]
  rw [htame]
  constructor
  · intro hx y hy
    rw [← hdy y hy]
    obtain ⟨n, xs, hxs, hcs⟩ := hs
    have H := GlobalTheory.SmGL.depthZeroSupport _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hx)
    rw [← hxs] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨v, hv, hv0⟩ := H i
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  · intro H
    exact hDZI _ x (msupp m) hs fun y hy => (hdy y hy).2 (H y hy)

end GlobalTheory.LlcDepth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRestrictScalarsHomMaximalRealSubfield
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

open scoped Topology
namespace GlobalTheory

theorem restrictScalarsHom_maximalRealSubfield_continuous :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω],
    Continuous (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* G (maximalRealSubfield E) Ω) := by
  intro E Ω _ _ _ _ _
  set F := maximalRealSubfield E
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis F M
  set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def
  have hMt : M ≤ IntermediateField.adjoin F t := by
    intro m hm
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    rw [← h]
    exact sum_mem fun i _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F t (Set.mem_range_self i))
  have hint : ∀ x ∈ t, IsIntegral E x := by
    rintro x ⟨i, rfl⟩
    have : IsIntegral F (b i) := IsIntegral.of_finite F _
    exact (IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top
  haveI : Finite t := Set.finite_range _
  haveI : FiniteDimensional E (IntermediateField.adjoin E t) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩
  have hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictScalarsHom F (A := Ω) (S := E))
        (IntermediateField.adjoin E t).fixingSubgroup) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro f ⟨τ, hτ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      (IntermediateField.subset_adjoin E _ hx)
  exact IntermediateField.fixingSubgroup_antitone hMt
    ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.CompIndep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_mem_map_of_prod {R : Type} [CommRing R] [IsDedekindDomain R] (f : R →+* R) (A I : Ideal R) (m p : R) (hm : m ≠ 0)
    (h : A * A.map f = Ideal.span {m}) (h1 : A * I * (A * I).map f = Ideal.span {m * p}) :
    ∀ b ∈ A.map f, p * b ∈ (A * I).map f := by
  intro b hb
  have h0 : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  rw [Ideal.map_mul, ← Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm, h] at h1
  have h2 := mul_left_cancel₀ h0 h1
  have h3 : p ∈ I.map f := by
    have h4 := Ideal.mem_span_singleton_self p
    rw [← h2] at h4
    exact (Ideal.mul_le_inf h4).2
  rw [Ideal.map_mul, mul_comm p]
  exact Ideal.mul_mem_mul hb h3

theorem smul_pull {R : Type} [CommRing R] {n : ℕ} (κ : Matrix (Fin n) (Fin n) R) (M p : ℕ) (v y : Fin n → R)
    (e : κ *ᵥ (p • v) - p • v = (M * p) • y) : p • (κ *ᵥ v - v) = p • M • y := by
  rw [smul_sub, ← Matrix.mulVec_smul, e, mul_comm M p, mul_smul]

theorem ratio_mul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p) (hI : l₂.Mb = l.Mb * I) :
    ∀ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), (p : 𝓞 E) * b ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 := l₂.prod
  rw [hI, hM, Nat.cast_mul] at h1
  rw [hI]
  refine mul_mem_map_of_prod _ _ _ _ _ (Nat.cast_ne_zero.2 ?_) l.prod h1
  have := l.three_le
  omega

theorem congr_of_marked {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (M p : ℕ) (hp : p ≠ 0)
    (J J₂ : Ideal (𝓞 D.host.E)) (hJ : ∀ b ∈ J, (p : 𝓞 D.host.E) * b ∈ J₂) (g g' k : GA D V)
    (hk : finHom V k = finHom V (g⁻¹ * g')) (hL : latG V g = latG V g')
    (x : La → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hm : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g,
      x a - (finHom V g).1.mulVec (finVec V (ι a)) = (M * p) • w)
    (hm' : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g',
      x a - (finHom V g').1.mulVec (finVec V (ι a)) = (M * p) • w) :
    ∀ b ∈ J, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M J).2 fun v hv => ?_
  have hH : latGHat V g' = latGHat V g := by
    rw [GlobalTheory.RecDict.coset_latGHat, GlobalTheory.RecDict.coset_latGHat, hL]
  have hv' : v ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := by
    rw [Submodule.map_smul'', Submodule.map_top, hι.2]
    exact hv
  obtain ⟨a, ha, rfl⟩ := hv'
  have hpa : p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La) := by
    refine Submodule.smul_induction_on (p := fun a => p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La)) ha
      (fun b hb c _ => ?_) (fun s t hs ht => ?_)
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul]
      exact Submodule.smul_mem_smul (hJ b hb) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hs ht
  obtain ⟨w, hw, e⟩ := hm _ hpa
  obtain ⟨w', hw', e'⟩ := hm' _ hpa
  rw [hH] at hw'
  obtain ⟨y, hy, ey⟩ := GlobalTheory.RecDict.coset_fin (latGHat V 1) (latGHat V g) (finHom V g) (finHom V g') 1 (M * p)
    (fun u hu => ((GlobalTheory.MarkCoset.latG_spec D V g).2 u).1 hu) (fun u hu => by simpa using hu)
    (fun u hu => by simpa using hu) _ _ w w' 0 hw hw' (zero_mem _) e e' (by simp)
  refine ⟨y, hy, ?_⟩
  have hf : finVec V (ι (p • a)) = p • finVec V (ι a) := by
    rw [map_nsmul]
    exact AdLat.cap_fv_nsmul D.host.F p _
  rw [hf, one_mul, ← map_inv, ← map_mul, ← hk] at ey
  funext i
  exact GlobalTheory.MarkCoset.nsmul_cancel D.host.F p (Nat.cast_ne_zero.2 hp) (congrFun (smul_pull _ M p _ y ey) i)

theorem comp_eq_of_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  intro D T hT j hj σ hσ C hC h h' hh
  obtain ⟨⟨-, hM, -, hI, -⟩, -, -, -, -, hr, g, e, F, ik, φ, th, -, -, -, hd⟩ := hC
  obtain ⟨hr', -, -, -, -, -, -, hι, -⟩ := hT.adPin j hj σ hσ
  obtain ⟨th', hr'', -, hQ, hK, ⟨x0, -, hR⟩, -⟩ := hT.dictU j hj σ hσ
  obtain ⟨γ, hγ, hΛ, hm, -⟩ := hd h
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hd h'
  rw [← hh] at hΛ' hm'
  have hinj : Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hL : latG (T.V j σ) (γ * h) = latG (T.V j σ) (γ' * h') :=
    SetLike.coe_injective (hinj.image_injective (hΛ.symm.trans hΛ'))
  obtain ⟨a, ha, k, hk, eak⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ * h)⁻¹ * (γ' * h'))
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hM, h0] at this
    omega
  have hk' : k ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k).2 ⟨hk, ?_⟩
    have hm₁ := hm
    have hm₂ := hm'
    rw [hM] at hm₁ hm₂
    exact congr_of_marked (T.V j σ) _ hι _ _ hp _ _ (ratio_mul_mem T.Q.l C.d.l₂ _ _ hM hI) (γ * h) (γ' * h') k
      (by rw [eak, map_mul, show finHom (T.V j σ) a = 1 from ha, one_mul]) hL _ hm₁ hm₂
  have q : ∀ δ ∈ GQ (T.V j σ), ∀ u, (T.dict j σ (δ * u)).1 = (T.dict j σ u).1 := fun δ hδ u => by
    obtain ⟨_, -, e⟩ := hQ δ hδ u
    rw [e]
  have q₁ : (T.dict j σ (γ * h * a * k)).1 = (T.dict j σ (γ * h * a)).1 := by
    obtain ⟨_, -, e⟩ := hK k hk' (γ * h * a)
    rw [e]
  have q₂ : (T.dict j σ (γ * h * a)).1 = (T.dict j σ (γ * h)).1 := by
    obtain ⟨_, -, e⟩ := hR (γ * h) a ha
    rw [e]
  rw [← q γ hγ h, ← q γ' hγ' h', ← q₂, ← q₁, mul_assoc (γ * h), ← eak, mul_inv_cancel_left]

end GlobalTheory.CoverRead.CompIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem galoisLatticeAction_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) (g h : ↥(GK K)) :
    actT L g ∘ₗ actT L h = actT L (g * h) := by
  ext x
  simp [actT, map_mul]
  rfl

theorem galoisLatticeAction_one {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) :
    actT L 1 = LinearMap.id := by
  ext x
  simp [actT, map_one]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem isUnit_toMatrix_actT {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : ↥(GK K)) :
    IsUnit (LinearMap.toMatrix b b (actT L g)) := by
  have h1 : LinearMap.toMatrix b b (actT L g) * LinearMap.toMatrix b b (actT L g⁻¹) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, mul_inv_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  have h2 : LinearMap.toMatrix b b (actT L g⁻¹) * LinearMap.toMatrix b b (actT L g) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, inv_mul_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem clause1_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  intro l _ K P AI hStd V _ _ _ _ _ _ _ ρ L hcont hcrys
  haveI : Module.Free ℤ_[l] ↥L.T := L.free
  haveI : Module.Finite ℤ_[l] ↥L.T := Module.Finite.iff_fg.mpr L.fg
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_breuilKisin_frobenius_period l K bk
  let b := Module.finBasis ℤ_[l] ↥L.T
  obtain ⟨s⟩ := GlobalTheory.T.exists_crystalline_lattice_periods_on_disc l K bk τ hτ P AI hStd V ρ L hcont hcrys _ b
  have hu : ∀ g, IsUnit (LinearMap.toMatrix b b (actT L g)) := fun g => isUnit_toMatrix_actT L b g
  obtain ⟨hs⟩ := GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer l K bk τ hτ _ _ hu s
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice l K bk τ hτ _ _ hu s hs
  obtain ⟨M, e, hMe⟩ := GlobalTheory.T.exists_framed_fCrystal_of_stratifiedPhiModule l K bk _ S
  exact ⟨M, GlobalTheory.T.etaleRealisation_of_framedMatrices l K bk _ S M e hMe ↥L.T (fun g => actT L g) b T hST⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspSubZeroVEqTop
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory

theorem cuspSub_zero_V_eq_top {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (π : CuspSub E 0) :
    π.V = ⊤ := by
  have hsub : Subsingleton (GA E 0) := inferInstance
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have h1 : (φ : GA E 0 → ℂ) 1 ≠ 0 := by
    intro h
    apply hφ0
    ext g
    rw [Subsingleton.elim g 1]
    simpa using h
  rw [eq_top_iff]
  intro ψ _
  have e : ψ = ((ψ : GA E 0 → ℂ) 1 / (φ : GA E 0 → ℂ) 1) • φ := by
    ext g
    rw [Subsingleton.elim g 1]
    simp [div_mul_cancel₀ _ h1]
  rw [e]
  exact π.V.smul_mem _ hφ

theorem cuspSub_zero_V_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (π π' : CuspSub E 0), π.V = π'.V := by
  intro E _ _ _ π π'
  rw [cuspSub_zero_V_eq_top π, cuspSub_zero_V_eq_top π']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfHasSupportSingleton
section
noncomputable section

open ValuativeRel GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.GenericUnitary GlobalTheory.KTypeTest GlobalTheory.KTypeDatum GlobalTheory.DZero
  GlobalTheory.DZeroHecke

namespace GlobalTheory.DZeroDegOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_hasSupport_singleton {y z : IrrGL k} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => z.1) hd) _).1
    (piTensor fun _ => z.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)) hi z.2.rep.irr
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

end GlobalTheory.DZeroDegOne
end
end

