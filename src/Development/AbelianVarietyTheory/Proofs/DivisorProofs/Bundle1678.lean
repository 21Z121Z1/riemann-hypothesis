import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField
open GlobalTheory.AbelianProjective

theorem exists_affine_loci_of_normChart : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∀ N₀ : LB B.left, N₀.IsLB → NormChart B N₀ → ∃ (I : Type) (t : I → N₀.Sec), (⨆ i, Out.nonzeroLocus (t i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (t i)) := by
  intro Ω _ _ B _ hB N₀ hN₀ ⟨W, V, π, a, U, N, n, hfin, hop, hne, hlft, hU, hUne, hN, H, hn⟩
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion a.left
  choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)
  refine ⟨_, t, ?_, fun w => ?_⟩
  · by_contra hne'
    have hc : ((⨆ i, Out.nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne' (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨w, hw⟩ := exists_fibre_mem π a U hUne (Out.nonzeroLocus n) (fun x => (hn x).2) y
    refine hy (IsLocalRing.closedPoint Ω) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)
    rw [ht]
    exact hw _
  · have hle : Out.nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U :=
      (ht w).trans_le (fibre_le π a U (Out.nonzeroLocus n) (fun x => (hn x).1) w)
    have := isIso_transl_left (w ≫ a)
    have : IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)
    rwa [inf_eq_left.2 hle] at h

theorem exists_normChart : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ N₀ : LB A.left, N₀.IsLB ∧ NormChart A N₀ := by
  intro K _ B _ hB
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩
  obtain ⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩ := GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have : Smooth A.hom := smooth_affineSpace K g
  have : IsIntegral A.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsAffine A.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (W₀.ι ≫ B.hom)
  let V : Over (Spec (CommRingCat.of K)) := Over.mk (V₀.ι ≫ A.hom)
  let π : W ⟶ V := Over.homMk π₀ hπ
  let a : W ⟶ B := Over.homMk W₀.ι rfl
  let j : V ⟶ A := Over.homMk V₀.ι rfl
  have : IsFinite π.left := hfin
  have : Flat π.left := hflat
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  have : Nonempty W.left := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))
  have : IsFinite (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have : Flat (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have hj : IsOpenImmersion (j ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›
  have : Smooth (A ⊗ B).hom := inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))
  have : QuasiCompact (A ⊗ B).hom := inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))
  have : IsLocallyNoetherian (A ⊗ B).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom
  have : CompactSpace (A ⊗ B).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom
  have : IsIntegral (A ⊗ B).left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)
  have : IsLocallyNoetherian (V ⊗ B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left
  obtain ⟨N, n, hN, hn⟩ := GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left)
    (GlobalTheory.secPull s _) (pull_isLB hL _)
  rw [GlobalTheory.nonzeroLocus_secPull, hs] at hn
  obtain ⟨N', hN', hφ⟩ := GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN
  obtain ⟨N₀, hN₀, hψ⟩ := GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'
  have e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have H : LBIso N (N₀.pull (snd V B).left) :=
    LBIso.trans hN (pull_isLB hN' _) (pull_isLB hN₀ _) (LBIso.symm hφ)
      (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)
  exact ⟨N₀, hN₀, W, V, π, a, U, N, n, hfin, inferInstance, inferInstance, inferInstance, hU, ⟨_, hxU⟩, hN, H, hn⟩

theorem isProjBy_of_cover_baseChange {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (A : Over (Sp K)) [IsProper A.hom]
    {B : Over (Sp Ω)} {φ : B.left ⟶ A.left} (h : IsPullback φ B.hom A.hom (spMap i)) {N₀ : LB A.left} (hN₀ : N₀.IsLB)
    {I : Type} (t : I → (N₀.pull φ).Sec) (hc : ⨆ j, Out.nonzeroLocus (t j) = ⊤)
    (ha : ∀ j, IsAffineOpen (Out.nonzeroLocus (t j))) : GlobalTheory.AbLaw.IsProjBy A.hom := by
  have : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have hN := pull_isLB hN₀ φ
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun j => (Out.nonzeroLocus (t j) : Set B.left))
    (fun j => (Out.nonzeroLocus (t j)).isOpen) fun x _ => by
      have hx : x ∈ ⨆ j, Out.nonzeroLocus (t j) := by rw [hc]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  have hamp : GlobalTheory.IsAmpleLB (N₀.pull φ) := GlobalTheory.isAmpleLB_of_cover hN le_rfl
    (fun j : F => GlobalTheory.secToPow (t j.1) 1) (top_unique fun x _ => by
      obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j, hj⟩, ?_⟩
      rw [GlobalTheory.nonzeroLocus_secToPow _ le_rfl]
      exact hx)
    fun j => (GlobalTheory.nonzeroLocus_secToPow (t j.1) le_rfl).symm ▸ ha j.1
  exact GlobalTheory.ProjFinite.isProjBy_of_fieldExtension i h hN₀ hN (GlobalTheory.lbIso_refl hN)
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 hamp)

theorem isProjBy_of_isAbelianScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  obtain ⟨N₀, hN₀, hc⟩ := exists_normChart K A hA
  let Ω := AlgebraicClosure K
  let B : Over (Sp Ω) := (Over.pullback (spMap (algebraMap K Ω))).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap (algebraMap K Ω))) B.hom A.hom (spMap (algebraMap K Ω)) :=
    IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨I, t, hcov, ha⟩ := exists_affine_loci_of_normChart Ω B hB _ (pull_isLB hN₀ _) (GlobalTheory.T.normChartLineBundle_baseChange_field_extension K Ω A hA N₀ hN₀ hc)
  exact isProjBy_of_cover_baseChange _ A sqB hN₀ t hcov ha
end GlobalTheory.ProjField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberField
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.NormTower

open IntermediateField

theorem abs_norm_coeff_zero_pow (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X])
    (h : GlobalTheory.FunObj.SqNum.IsMinPol σ β p) (hβ : IsAlgebraic ℚ β) :
    |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree =
      |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  obtain ⟨hm, hirr, hev⟩ := h
  haveI := Fact.mk hirr
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot p) := pb.finite
  haveI : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans K (AdjoinRoot p)
  set r := AdjoinRoot.root p
  have hNK : Algebra.norm K r = (-1) ^ p.natDegree * p.coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hm, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at this
  let φ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ β hev
  have hφ : φ r = β := AdjoinRoot.lift_root hev
  have hmin : minpoly ℚ r = minpoly ℚ β := by
    rw [← hφ]; exact (minpoly.algHom_eq φ.toRatAlgHom φ.injective r).symm
  have hint : IsIntegral ℚ r := .of_finite ℚ r
  have h1 : Algebra.norm ℚ r = Algebra.norm ℚ ((-1) ^ p.natDegree * p.coeff 0 : K) := by
    rw [← hNK, Algebra.norm_norm]
  have h2 := Algebra.norm_eq_norm_adjoin ℚ r
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ r) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  have hdeg : Module.finrank ℚ (AdjoinRoot p) = p.natDegree * Module.finrank ℚ K := by
    rw [← Module.finrank_mul_finrank ℚ K (AdjoinRoot p), pb.finrank, AdjoinRoot.powerBasis_dim, mul_comm]
  have hdeg2 : Module.finrank ℚ (AdjoinRoot p) = (minpoly ℚ β).natDegree * Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮r⟯ (AdjoinRoot p), IntermediateField.adjoin.finrank hint, hmin]
  have hn1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]; simp
  have key : |Algebra.norm ℚ (p.coeff 0)| = |(minpoly ℚ β).coeff 0| ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    have e := congrArg abs (h1.symm.trans (h2.trans (congrArg (· ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p)) h3)))
    rw [map_mul, map_pow, abs_mul, abs_pow, hn1, one_pow, one_mul, abs_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul] at e
    exact e
  rw [key, ← pow_mul, mul_comm, ← hdeg2, hdeg]

end GlobalTheory.NormTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SplitWeight

theorem exps_eq_zero {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ)
    (h1 : Function.Injective φ) (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) (c : I → ℤ)
    (h : ∀ k : L, k ≠ 0 → ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ c i = 1) : c = 0 := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := GlobalTheory.HalfIntChars.emb_mul_indep σ hσ (Sum.elim c (-c)) (fun k hk => by
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have e3 := congrArg (· ^ 2) (h k hk)
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (c i), zpow_mul, zpow_natCast,
      GlobalTheory.HalfIntChars.unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg])
  funext i
  have := congrFun this (Sum.inl i)
  simpa using this

theorem embTau_inj (D : D7) : Function.Injective (Formalism.L2.Host.embTau D) := fun i j h =>
  D.eTau.injective (GlobalTheory.HalfIntChars.embPsi_inj D.host h)

theorem embTau_ne_conj (D : D7) (i j : D.what₂.Tau) :
    Formalism.L2.Host.embTau D i ≠ (starRingEnd ℂ).comp (Formalism.L2.Host.embTau D j) :=
  GlobalTheory.HalfIntChars.embPsi_ne_conj D.host (D.eTau i) (D.eTau j)

theorem prod_eq_one {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : HChar D.host.E) (k : D.what₂.Tau → ℤ)
    (hf : ∀ x, χ.f x ^ e = χ'.1 (finIdl D x)) (hk : χ'.HasInf (Formalism.L2.Host.embTau D) k)
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ - k τ) = 1 := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hne : ∀ τ, φ τ a ≠ 0 := fun τ => by simpa using ha
  have hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
    div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := χ'.2.2 u
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf] at hB
  have hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1 := by
    have := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  rw [hk u] at hB'
  set X := ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ)
  have hX : X ≠ 0 := by simp [X]
  have hX' : X = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ := eq_inv_of_mul_eq_one_left hA
  rw [hX', inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, zpow_mul]
  rw [div_eq_one_iff_eq]
  · have h2 := eq_inv_of_mul_eq_one_left hB'
    have hua : (u : D.host.E) = a := rfl
    rw [hua] at h2
    rw [h2, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [zpow_neg, inv_inv]
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hu τ)

theorem abs_weight_eq_abs_infType : ∀ {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : HChar D.host.E)
    (k : D.what₂.Tau → ℤ), (e = 1 ∨ e = -1) → (∀ x, χ.f x ^ e = χ'.1 (finIdl D x)) →
    χ'.HasInf (Formalism.L2.Host.embTau D) k → ∀ τ, |χ.n τ| = |k τ| := by
  intro D N χ e χ' k he hf hk τ
  have hc := exps_eq_zero (Formalism.L2.Host.embTau D) (embTau_inj D) (embTau_ne_conj D)
    (fun τ => e * χ.n τ - k τ) (fun a ha => prod_eq_one χ e χ' k hf hk a ha)
  have h := congrFun hc τ
  simp only [Pi.zero_apply, sub_eq_zero] at h
  rw [← h]
  rcases he with rfl | rfl <;> simp

end GlobalTheory.SplitWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2Statement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_mem_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  first | exact @GlobalTheory.WeilM.schA_memLp_two | exact GlobalTheory.WeilM.schA_memLp_two | (intros; apply GlobalTheory.WeilM.schA_memLp_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZero
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.GhostKer

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_frobenius (b : Ainf p O) : phiInv p O (WittVector.frobenius b) = b := by
  rw [WittVector.frobenius_eq_map_frobenius]
  unfold phiInv
  ext n
  simp only [WittVector.map_coeff]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

theorem frobenius_iterate_teichmuller (k : ℕ) (x : PreTilt O p) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[k] (WittVector.teichmuller p x) =
      WittVector.teichmuller p (x ^ p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]

variable (p O) in

def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by rw [ghost, iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghost_succ_xi {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (k : ℕ) :
    ghost p O (k + 1) (xi ε) = p := by
  have h : ghost p O (k + 1) (WittVector.teichmuller p (root ε)) = 1 := by
    rw [ghost, frobenius_iterate_teichmuller, WittVector.fontaineTheta_teichmuller, pow_succ',
      pow_mul, root, frobeniusEquiv_symm_pow_p, map_pow]
    have h0 := hε.zeta_zero
    simp only [zeta, Function.iterate_zero, id] at h0
    rw [h0, one_pow]
  change ghostHom p O (k + 1) (xi ε) = p
  unfold xi
  rw [map_sum]
  simp only [map_pow]
  change ∑ i ∈ Finset.range p, (ghost p O (k + 1) (WittVector.teichmuller p (root ε))) ^ i = p
  simp [h]

theorem nu_eq_mu_root (x : PreTilt O p) : nu x = mu (root x) := rfl

end SlopeTestRemainingChoices

theorem mu_dvd_of_ghost : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
  have key : ∀ n, ∀ a : Ainf p O, (∀ m, ghost p O m a = 0) → mu ε ∣ mu (root^[n] ε) * a := by
    intro n
    induction n with
    | zero => intro a _; exact dvd_mul_right _ _
    | succ n ih =>
      intro a ha
      have ha0 : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
        rw [RingHom.mem_ker]; exact ha 0
      rw [GlobalTheory.AinfXi.ker_theta hv ε h1, Ideal.mem_span_singleton] at ha0
      obtain ⟨b, rfl⟩ := ha0
      have hb : ∀ m, ghost p O m (WittVector.frobenius b) = 0 := by
        intro m
        rw [ghost_frobenius]
        have h3 := ha (m + 1)
        rw [ghost_mul, ghost_succ_xi hε] at h3
        exact (mul_eq_zero.1 h3).resolve_left hp0
      obtain ⟨c, hc⟩ := ih _ hb
      have hc' := congrArg (phiInv p O) hc
      have e : root (root^[n] ε) = root^[n + 1] ε := (Function.iterate_succ_apply' root n ε).symm
      rw [map_mul, map_mul, phiInv_frobenius, phiInv_mu, phiInv_mu, nu_eq_mu_root, e] at hc'
      refine ⟨phiInv p O c, ?_⟩
      linear_combination xi ε * hc' + phiInv p O c * xi_mul_nu ε
  exact GlobalTheory.MuDivides.mu_dvd_of_forall_dvd p C v O hv ε h1 a (fun n => key n a ha)

end GlobalTheory.GhostKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

theorem alC_surjective_and_linearIndependent_bLie :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HTChar p v P.Gt → Function.Surjective P.alC ∧ ∀ (n : ℕ) (x : Fin n → LieG P.Gt), LinearIndependent C (fun j => evLie P (x j)) → LinearIndependent C (fun j => P.bLie (x j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hHT
  have hp : p.Prime := Fact.out
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : Function.Surjective P.alC := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro w -
    induction w using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul c f =>
      have h1 : v (algebraMap O C (p : O)) ^ (p - 1) ≤ v (p : C) := by
        have hle := P.integers.map_le_one (p : O)
        rw [map_natCast] at hle ⊢
        exact pow_le_of_le_one zero_le hle (by have := hp.two_le; omega)
      have h2 := hHT (p : O) h1 f.1 f.2
      rw [← (weilChar_surjective_and_map_range_al p C v O Λ P).2] at h2
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h2
      have h3 : P.al t = (p : O) • f := Subtype.ext ht
      refine ⟨(c * (p : C)⁻¹) • P.inclT t, ?_⟩
      rw [map_smul, P.alC_inclT, h3, map_smul, ← algebraMap_smul C (p : O), map_natCast, smul_smul,
        inv_mul_cancel_right₀ h0, Point.inclOm, TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
  refine ⟨hs, fun n x hx => LinearIndependent.of_comp P.pairV ?_⟩
  have e : (⇑P.pairV ∘ fun j => P.bLie (x j)) = ⇑P.alC.dualMap ∘ fun j => evLie P (x j) :=
    funext fun j => LinearMap.ext fun w => pairV_bLie_eq_evLie (x j) w
  rw [e]
  exact hx.map' _ (LinearMap.ker_eq_bot.2 (LinearMap.dualMap_injective_of_surjective hs))

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchSchwartzL2BoundedIntertwinerContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archSchwartz_L2Bounded_intertwiner_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (C : ℝ≥0∞), C ≠ ⊤ →
      (∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) →
      (∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf D.host.F ψ v ⇑f →
        ⇑(A f') = GlobalTheory.WeilAdm.schrInf D.host.F ψ (L v) ⇑(A f)) →
      Continuous A := by
  first | exact @GlobalTheory.WeilAdm.realcont | exact GlobalTheory.WeilAdm.realcont | (intros; apply GlobalTheory.WeilAdm.realcont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignaturesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines σ JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRepD.archRepD | exact GlobalTheory.ArchRepD.archRepD | (intros; apply GlobalTheory.ArchRepD.archRepD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLUniformModerateGrowthStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_uniform_moderate_growth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∃ N : ℕ, ∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod φ).1 (infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.AutGrowth.uniform_growth_of_autForm | exact GlobalTheory.AutGrowth.uniform_growth_of_autForm | (intros; apply GlobalTheory.AutGrowth.uniform_growth_of_autForm <;> assumption)
end

