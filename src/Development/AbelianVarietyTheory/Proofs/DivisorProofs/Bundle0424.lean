import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparableStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale D (integralClosure D (TensorProduct S D L)) := by
  first | (exact @GlobalTheory.abhyankar_dvr_of_isSeparable) | (exact GlobalTheory.abhyankar_dvr_of_isSeparable) | (intros; apply GlobalTheory.abhyankar_dvr_of_isSeparable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPow
section
open MeasureTheory Matrix

namespace GlobalTheory.HeisUnit

theorem exists_unitary_factor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  intro k _ _ _ _ n d ψ0 hψc hψ1 ι hι Tr Mu hTr hMu hTrI hMuI S hS hSI χ hχ
  let ν : kˣ →* ℂˣ := χ *
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  have hν : ∀ x : kˣ, (ν x : ℂ) = (χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := fun x => rfl
  have hfac : ∀ x : kˣ, (χ x : ℂ) = ν x * GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2) := fun x => by
    rw [hν, mul_assoc, ← GlobalTheory.SplitFlip.apow_add, neg_add_cancel, GlobalTheory.SplitFlip.apow_zero, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, fun x => by simp, fun g => ?_⟩
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  · refine ⟨ν, fun x => ?_, fun g => hfac _⟩
    let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨φ0, hφ0, hιφ0⟩ := hι.surjOn (GlobalTheory.HeisUnit.intInd_mem_SB (k := k) n d)
    have hne : φ0 ≠ 0 := by
      rintro rfl
      have h := congrFun hιφ0 0
      rw [map_zero, GlobalTheory.HeisUnit.intInd_zero] at h
      exact zero_ne_one h
    have hN : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤ := fun μ hμ =>
      ⟨(GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).2.2.1 hne, (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).1⟩
    have hU := GlobalTheory.T.norm_character_unit_eq_one_heisenberg ι hι.injOn S hS hSI χ hχ φ0 hφ0 hιφ0 hN i0
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
    have hP := GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one ι hι.injOn Tr hTr hTrI S hS hSI χ hχ φ0 hφ0 hιφ0 hne ϖ hϖ i0
      (fun μ hμ T T' h => GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal ψ0 hψc hψ1 ι hι.injOn Tr hTr Mu hMu hMuI φ0 hφ0 hιφ0 ϖ hϖ i0 T T' h μ hμ)
    rw [hν]
    exact GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one d χ hU ϖ hϖ hP x

end GlobalTheory.HeisUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionCartierDualTangentBijectiveStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFunctionCartierDualTangent_bijective : ∀ {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A], Function.Bijective (primTangent R A) := by
  first | exact @GlobalTheory.PDiv.primTangent_bijective | exact GlobalTheory.PDiv.primTangent_bijective | (intros; apply GlobalTheory.PDiv.primTangent_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionsFlatBaseChangeBijectiveStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFunctions_flatBaseChange_bijective : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'], Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  first | exact @GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective | exact GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective | (intros; apply GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeRepresentingQcQsFiniteType
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem representing_qc_qs_loft : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧
      LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H R
  classical
  let e : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex A B))) A B :=
    (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  set N := Fintype.card (Module.Free.ChooseBasisIndex A B)
  set ξ := R.homEquiv (𝟙 H) with hξ
  have hR : ∀ {Z : Scheme.{0}} (b : Z ⟶ H), R.homEquiv b = (functor A B r).map b.op ξ := by
    intro Z b
    have := R.homEquiv_comp b (𝟙 H)
    rwa [Category.comp_id] at this
  have hmap : ∀ {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (b : Z ⟶ H),
      (functor A B r).map a.op ((functor A B r).map b.op ξ) = (functor A B r).map (a ≫ b).op ξ := by
    intro Z Z' a b
    rw [← hR b, ← hR (a ≫ b), R.homEquiv_comp]
  have hrc : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z),
      Set.range (a ≫ b) = b '' Set.range a := by
    intro X Y Z a b
    ext p
    simp
  choose W hW hWc using fun σ : Fin r ↪ Fin N => GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ H ξ
  choose X x hXa hXl hXb hXu using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  have hcov : ⨆ σ, W σ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨σ, U, hU, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e H ξ h
    have := (hW σ _ U.ι).2 hb
    rw [Scheme.Opens.range_ι] at this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨σ, this hU⟩
  have hiso : ∀ σ, ∃ g : (W σ).toScheme ⟶ X σ, IsIso g ∧ (W σ).ι ≫ ξ.1 = g ≫ (x σ).1 := by
    intro σ
    have hb : Basic A B e σ ((functor A B r).map (W σ).ι.op ξ) :=
      (hW σ _ _).1 (by rw [Scheme.Opens.range_ι])
    obtain ⟨g, hg, -⟩ := hXu σ _ _ hb
    obtain ⟨f, hf⟩ : ∃ f, R.homEquiv f = x σ := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hfr : Set.range f ⊆ Set.range (W σ).ι := by
      rw [Scheme.Opens.range_ι]
      exact (hW σ _ f).2 (by rw [← hR, hf]; exact hXb σ)
    let f' := IsOpenImmersion.lift (W σ).ι f hfr
    have hf' : f' ≫ (W σ).ι = f := IsOpenImmersion.lift_fac _ _ _
    have hgf : g ≫ f = (W σ).ι := R.homEquiv.injective (by rw [R.homEquiv_comp, hf, hg, hR])
    have h1 : g ≫ f' = 𝟙 _ := by
      rw [← cancel_mono (W σ).ι, Category.assoc, hf', hgf, Category.id_comp]
    have h2 : f' ≫ g = 𝟙 _ := by
      obtain ⟨g0, -, hu⟩ := hXu σ (X σ) (x σ) (hXb σ)
      have e1 : (functor A B r).map (f' ≫ g).op (x σ) = x σ := by
        rw [← hf, ← R.homEquiv_comp, Category.assoc, hgf, hf']
      have e2 : (functor A B r).map (𝟙 (X σ)).op (x σ) = x σ := by simp
      exact (hu _ e1).trans (hu _ e2).symm
    exact ⟨g, ⟨f', h1, h2⟩, (congrArg Sigma.fst hg).symm⟩
  choose g hg hgx using hiso
  have hWa : ∀ σ, IsAffineOpen (W σ) := fun σ => by
    haveI := hg σ; haveI := hXa σ; exact IsAffine.of_isIso (g σ)
  have hint : ∀ (U : H.Opens), CompactSpace U.toScheme → ∀ τ, IsCompact ((U : Set H) ∩ W τ) := by
    intro U hU τ
    obtain ⟨V, hV, hVc⟩ := GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e τ U.toScheme ((functor A B r).map U.ι.op ξ)
    have key : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ U.toScheme),
        Set.range a ⊆ V ↔ U.ι '' Set.range a ⊆ W τ := fun Z' a => by
      rw [hV, hmap, ← hW, hrc]
    have hVeq : (V : Set U.toScheme) = U.ι ⁻¹' (W τ) := by
      apply subset_antisymm
      · have := (key _ V.ι).1 (by rw [Scheme.Opens.range_ι])
        rw [Scheme.Opens.range_ι] at this
        exact Set.image_subset_iff.1 this
      · have := (key _ (U.ι ⁻¹ᵁ W τ).ι).2 (by
          rw [Scheme.Opens.range_ι]; exact Set.image_preimage_subset _ _)
        rw [Scheme.Opens.range_ι] at this
        exact this
    have : (U : Set H) ∩ W τ = U.ι '' V := by
      rw [hVeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
    rw [this]
    exact (hVc hU).image U.ι.continuous
  have hWc' : ∀ σ, CompactSpace (W σ).toScheme := fun σ => by
    haveI : IsAffine (W σ).toScheme := hWa σ
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · rw [quasiCompact_iff_compactSpace]
    show CompactSpace H
    rw [← isCompact_univ_iff]
    have : (Set.univ : Set H) = ⋃ σ, (W σ : Set H) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hcov]; rfl
    rw [this]
    exact isCompact_iUnion fun σ => (hWa σ).isCompact
  · rw [quasiSeparated_iff_quasiSeparatedSpace]
    exact Scheme.quasiSeparatedSpace_of_isOpenCover W hcov hWa
      (fun σ τ => hint (W σ) (hWc' σ) τ)
  · haveI : IsZariskiLocalAtSource @LocallyOfFiniteType := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) W hcov fun σ => ?_
    rw [hgx σ]
    haveI := hg σ
    haveI := hXl σ
    infer_instance

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCompShuffleHomotopicIdStatement
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  first | (exact @GlobalTheory.EZ.awThen_homotopic) | (exact GlobalTheory.EZ.awThen_homotopic) | (intros; apply GlobalTheory.EZ.awThen_homotopic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupDegreeZeroSupportCochain
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.AWFront

theorem sub_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ev_of_front {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k)
    (hγ : μ.IsAW hk α β γ)
    (hα : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U) :
    ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega)))
      (ev β N _ rfl U x) := by
  have key : ∀ (s : ℤ) (hs : s = n) (H : s + (-(N : ℤ) + m) = w) (h1 : -((0 : ℕ) : ℤ) + n = s),
      μ.mul U s (-(N : ℤ) + m) w H (ev α 0 s h1 U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) =
        μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro s rfl H h1
    rfl
  have gen : ∀ (p : ℕ), p = 0 → ∀ (H : -(p : ℤ) + n + (-((N - p : ℕ) : ℤ) + m) = w) (h1 : 0 + p ≤ N)
      (h2 : p + (N - p) ≤ N),
      (m * (p : ℤ)).negOnePow • μ.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w H
        (ev α p _ rfl U (x.sub 0 p h1)) (ev β (N - p) _ rfl U (x.sub p (N - p) h2)) =
      μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro p rfl H h1 h2
    have e1 : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub 0 (N - 0) h2 = x := sub_full x h2
    rw [e2]
    exact key _ (by simp) H rfl
  rw [hγ N w h U x, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · exact gen _ (by simp) _ _ _
  · rw [hα (i.succ : ℕ) _ rfl U _ (by simp), map_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.AWFront
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_cechNerveAugmentation_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S), ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U) (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U), e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_iso) | (exact GlobalTheory.EtC.bc_cechAug_iso) | (intros; apply GlobalTheory.EtC.bc_cechAug_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLiftClassFunction
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_lift_class_function : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), IsCl f → (∀ δ γ, IsNorm s δ γ → shLift s f δ = f γ) ∧ ∀ δ y : GL (Fin n) F', shLift s f (y⁻¹ * δ * galAct F F' n s y) = shLift s f δ := by
  first | (exact @GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (exact GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (intros; apply GlobalTheory.Shin.shLift_isNorm_and_twisted_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSqStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  first | exact @GlobalTheory.PDiv.cotMap_injective_of_sq | exact GlobalTheory.PDiv.cotMap_injective_of_sq | (intros; apply GlobalTheory.PDiv.cotMap_injective_of_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycleStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgebraPullbackTwo_convMul_symmetricCocycle : ∀ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A), c ∈ symCocycles R A → pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c + cobOne R B (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  first | exact @GlobalTheory.PDiv.pullTwo_convMul | exact GlobalTheory.PDiv.pullTwo_convMul | (intros; apply GlobalTheory.PDiv.pullTwo_convMul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveBaseChangeDescendsFilteredColimitStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_baseChange_descends_filteredColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  first | (exact @GlobalTheory.BijDescent.bijective_of_isColimit) | (exact GlobalTheory.BijDescent.bijective_of_isColimit) | (intros; apply GlobalTheory.BijDescent.bijective_of_isColimit  <;> assumption)
end

