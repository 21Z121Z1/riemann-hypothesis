import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniform
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySublistPadding
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

universe u

theorem sub_positions_univ {α : Type u} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    ∃ o : Fin (sub W c i).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
      ∀ a, (sub W c i).get a = W.get (o a) := by
  have key : ∀ L : List (Fin W.length), L.Pairwise (· < ·) → (∀ j, j ∈ L ↔ c j = i) →
      ∃ o : Fin (L.map W.get).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
        ∀ a, (L.map W.get).get a = W.get (o a) := by
    intro L hpw hmem
    have hlen : (L.map W.get).length = L.length := by simp
    refine ⟨fun a => L.get (Fin.cast hlen a), ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : Fin.cast hlen a < Fin.cast hlen b := by
        first
        | exact hab
        | simpa [Fin.lt_def] using hab
      exact List.pairwise_iff_get.1 hpw (Fin.cast hlen a) (Fin.cast hlen b) hab'
    · intro j
      constructor
      · intro hj
        obtain ⟨n, hn⟩ := List.mem_iff_get.1 ((hmem j).2 hj)
        refine ⟨Fin.cast hlen.symm n, ?_⟩
        first
        | exact hn
        | simpa using hn
      · rintro ⟨a, rfl⟩
        exact (hmem _).1 (List.mem_iff_get.2 ⟨_, rfl⟩)
    · intro a
      simp [List.get_eq_getElem]
  exact key ((List.finRange W.length).filter (fun p => decide (c p = i)))
    ((List.pairwise_lt_finRange _).filter _) (fun j => by simp)

end GlobalTheory.CompanionTheory.FineProd

namespace GlobalTheory.CompanionTheory.FineProd

theorem jm_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (W : List (IrrGL k)) (c : Fin W.length → Fin h) (i : Fin h) (Y : Fin W.length → IrrGL k), (∀ j, c j = i → Y j = W.get j) → (∀ j, c j ≠ i → (Y j).1 = 0) → ∀ (hd : ∑ j, (Y j).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm Y hd π = jmL (sub W c i) π := by
  intro k _ _ _ _ h N W c i Y hY h0 hd V _ _ π
  obtain ⟨o, ho, hr, hg⟩ := sub_positions_univ W c i
  have hget : (sub W c i).get = fun a => Y (o a) := by
    funext a
    rw [hg a, hY (o a) ((hr (o a)).2 ⟨a, rfl⟩)]
  have hsum : ∑ a, (Y (o a)).1 = N := by
    rw [← hd]
    have himg : ∑ j ∈ Finset.univ.image o, (Y j).1 = ∑ a, (Y (o a)).1 :=
      Finset.sum_image (fun a _ b _ e => ho.injective e)
    rw [← himg]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro j _ hj
    refine h0 j ?_
    intro e
    obtain ⟨a, rfl⟩ := (hr j).1 e
    exact hj (Finset.mem_image_of_mem o (Finset.mem_univ a))
  have hnz : ∀ j, (Y j).1 ≠ 0 → j ∈ Set.range o := by
    intro j hj
    refine (hr j).1 ?_
    by_contra e
    exact hj (h0 j e)
  have hdeg : ∑ a, ((sub W c i).get a).1 = N := by
    rw [hget]
    exact hsum
  have hcongr : ∀ {r : ℕ} (x y : Fin r → IrrGL k) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N),
      x = y → jm x hx π = jm y hy π := by
    intro r x y hx hy e
    subst e
    rfl
  rw [GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks Y hd o ho hnz hsum π, jmL, dif_pos hdeg]
  exact hcongr _ _ _ _ hget.symm

end GlobalTheory.CompanionTheory.FineProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorLiftDominantStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_vector_lift_dominant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ w ∈ fixed (D.piN π) D.JT, ∃ j : ℕ, ∃ v : fixed π D.J, D.proj π (v : V) = D.piN π (t ^ j) w := by
  first | exact @GlobalTheory.CompanionTheory.CassPush.exists_fixed_proj_eq_piN_pow | exact GlobalTheory.CompanionTheory.CassPush.exists_fixed_proj_eq_piN_pow | (intros; apply GlobalTheory.CompanionTheory.CassPush.exists_fixed_proj_eq_piN_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniformStatement
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_sum_bound_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (δ : ℝ) (α : GA E N → ℂ) (F Ω : Set (GA E N)),
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ → IsCompact Ω →
  ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ (n : ℕ) (ψ : Fin n → GA E N → ℂ), (∀ i, Continuous (ψ i)) →
    (∀ i, ∀ γ ∈ latticeGL E N, ∀ x, ψ i (γ * x) = ψ i x) →
    (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ i (x * y) ∂μ = s * ψ i x) →
    (∀ i, (∫⁻ x in F, ‖ψ i x‖ₑ ^ 2 ∂μ) = 1) →
    (∀ i j, i ≠ j → ∫ x in F, ψ i x * (starRingEnd ℂ) (ψ j x) ∂μ = 0) →
    ∑ i, ∫⁻ x in Ω, ‖ψ i x‖ₑ ^ 2 ∂μ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le | exact GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le | (intros; apply GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Right

variable {K : Type} [Field K]

theorem inU_pre (hs : SiteLaws) {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)} {r : Y ⟶ Spec (CommRingCat.of K)}
    (u : Y ⟶ Z) (hu : u ≫ p = r) (V : Z.Opens) (T) : inU r (u ⁻¹ᵁ V) T ↔ inU p V ((smS u hu).G.obj T) := by
  subst hu
  exact (hs K Z Z Y p (𝟙 Z) u).2.2.2.2.1 V T

theorem inU_biInf (hs : SiteLaws) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) {κ : Type} (V : κ → Z.Opens)
    (S : Finset κ) (T) : inU q (⨅ α ∈ S, V α) T ↔ ∀ α ∈ S, inU q (V α) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K Z Z Z q (𝟙 Z) (𝟙 Z)
  rw [← Finset.inf_eq_iInf]
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

theorem capU_of_forall {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C)
    (Q : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty) (h : ∀ T, Q T ↔ ∀ α ∈ S, U α T) : capU U S = Q := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

theorem capU_empty_eq {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C) :
    (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem res_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C)
    (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  exact ⟨fun a b e => by rwa [h, h] at e, fun y => ⟨y, h y⟩⟩

theorem res_bij_of_eq {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U Q Q' : ObjectProperty C} (e : Q = Q') (h : Q ≤ U) (h' : Q' ≤ U) (n : ℕ)
    (hb : Function.Bijective ((resU F h).pull n)) : Function.Bijective ((resU F h').pull n) := by
  subst e
  exact hb

theorem kun_congr (E : XD K) {U₁ : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D}
    (e₂ : U₂ = U₂') (e₃ : U₃ = U₃') (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁ (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (h : E.Kun U₁ U₂ U₃ h₁ h₂) :
    E.Kun U₁ U₂' U₃' h₁' h₂' := by
  subst e₂ e₃
  exact h

theorem kun_right : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hs hmv hcd hz hA hK K _ _ X X' P q q' _ _ p₁ p₂ hP V d cV h₁ h₂
  classical
  obtain ⟨U⟩ := (cov_ex q').1 inferInstance
  have hw : p₂ ≫ q' = p₁ ≫ q := hP.w.symm
  obtain ⟨hcosP, -, htopP, hinfP, -, -⟩ := hs K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)
  obtain ⟨hcos', -, htop', -, -, -⟩ := hs K X' X' X' q' (𝟙 X') (𝟙 X')
  have l₁ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q V ((smS p₁ rfl).G.obj T) :=
    fun D T hT => (inU_pre hs p₁ rfl V T).1 ((hinfP _ _ T).1 hT).1
  have l₂ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q' D ((smS p₂ hw).G.obj T) :=
    fun D T hT => (inU_pre hs p₂ hw D T).1 ((hinfP _ _ T).1 hT).2
  let E := hodgeXD q q' p₁ p₂ hw
  let Vv : U.ι → ObjectProperty E.C₂ := fun α => inU q' (U.U α)
  let Ww : U.ι → ObjectProperty E.D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α)
  have g₁ : ∀ (S : Finset U.ι) T, capU Ww S T → inU q V (E.L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, -⟩
    exact l₁ _ T hα
  have g₂ : ∀ (S : Finset U.ι) T, capU Ww S T → capU Vv S (E.L₂.obj T) := by
    rintro S T ⟨⟨α, hα⟩, hS⟩
    exact ⟨⟨α, l₂ _ T hα⟩, fun β hβ => l₂ _ T (hS β hβ)⟩
  have eV : ∀ S : Finset U.ι, S.Nonempty → capU Vv S = inU q' (⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => inU_biInf hs q' U.U S T
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      capU Ww S = inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => by
      obtain ⟨α₀, hα₀⟩ := hS
      rw [hinfP, inU_pre hs p₂ hw, inU_biInf hs q' U.U S]
      refine ⟨fun h α hα => (hinfP _ _ T).2 ⟨h.1, (inU_pre hs p₂ hw _ T).2 (h.2 α hα)⟩, fun h => ⟨((hinfP _ _ T).1 (h α₀ hα₀)).1, fun α hα => (inU_pre hs p₂ hw _ T).1 ((hinfP _ _ T).1 (h α hα)).2⟩⟩
  have hS : ∀ S : Finset U.ι, S.Nonempty → E.Kun (inU q V) (capU Vv S) (capU Ww S) (g₁ S) (g₂ S) := by
    intro S hne
    obtain ⟨α₀, hα₀⟩ := id hne
    obtain ⟨c', -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ hα₀) (U.inter S hne)
    exact kun_congr E (eV S hne).symm (eW S hne).symm (l₁ _) (l₂ _) _ _
      (GlobalTheory.T.kuenneth_product_local_coords hs hA hK K X X' P q q' p₁ p₂ hP V _ d _ cV ⟨c'⟩ (l₁ _) (l₂ _))
  have hglue := GlobalTheory.T.kuenneth_mayer_vietoris_left hmv hcd E (inU q V) Vv Ww (fun α => hcos' _) (fun α => hcosP _) g₁ g₂ hS
  have k₂ : capU Vv ∅ ≤ inU q' ⊤ := fun T _ => htop' T
  have k₃ : capU Ww ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (hinfP _ _ T).2 ⟨((hinfP _ _ T).1 hα).1, (inU_pre hs p₂ hw _ T).2 (htop' _)⟩
  have sup₃ : (⨆ α, p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) = p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤ := by
    rw [← inf_iSup_eq, ← U.cover]
    congr 1
    ext x
    simp [TopologicalSpace.Opens.mem_iSup]
  refine (GlobalTheory.T.kuenneth_of_restrict_bijective E h₁ h₂ (g₁ ∅) (g₂ ∅) (le_refl _) k₂ k₃ ?_ ?_ ?_).2 hglue
  · exact fun a n => res_self_bij _ _ _ n
  · intro a n
    exact res_bij_of_eq (G q' a) (capU_empty_eq Vv) (fun _ _ => htop' _) k₂ n
      (hz K X' q' U.ι ⊤ U.U U.cover _ a n)
  · intro a n
    refine res_bij_of_eq (G (p₁ ≫ q) a) (capU_empty_eq Ww) (fun T hT => k₃ T ((capU_empty_eq Ww ▸ hT : capU Ww ∅ T))) k₃ n
      (hz K P (p₁ ≫ q) U.ι _ (fun α => p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) sup₃ _ a n)

end GlobalTheory.CompanionTheory.KunGlue.Right
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormulaStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_character_tame_formula : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  first | exact @GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup | exact GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup | (intros; apply GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LdpContDiffOn
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Dm (n : ℕ) : Set (Mat n × Mat n) := GLs n ×ˢ GLs n

def Ldp (X : Mat n) (K : Mat n × Mat n → V) : Mat n × Mat n → V := fun p => fderiv ℝ K p (0, X * p.2)

def Hw (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) : Mat n × Mat n → V :=
  w.foldr (fun p h => Ldp (bs p) h) K

def Hf (f : Mat n → V) : Mat n × Mat n → V := fun p => f (p.1⁻¹ * p.2)

@[simp] theorem Hw_nil (K : Mat n × Mat n → V) : Hw [] K = K := rfl

theorem Hw_cons (p : Bool × Fin n × Fin n) (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) :
    Hw (p :: w) K = Ldp (bs p) (Hw w K) := rfl

theorem isOpen_Dm : IsOpen (Dm n) := GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs

def fld (X : Mat n) : (Mat n × Mat n) →L[ℝ] (Mat n × Mat n) :=
  (ContinuousLinearMap.inr ℝ (Mat n) (Mat n)).comp ((GlobalTheory.CompanionTheory.RCalc.mulL X).comp (ContinuousLinearMap.snd ℝ (Mat n) (Mat n)))

theorem fld_apply (X : Mat n) (p : Mat n × Mat n) : fld X p = (0, X * p.2) := rfl

theorem Ldp_contDiffOn (X : Mat n) {K : Mat n × Mat n → V} (hK : ContDiffOn ℝ ∞ K (Dm n)) :
    ContDiffOn ℝ ∞ (Ldp X K) (Dm n) :=
  GlobalTheory.CompanionTheory.RCalc.contDiffOn_fderiv_field isOpen_Dm hK (fld X)

theorem Hw_contDiffOn (w : List (Bool × Fin n × Fin n)) {K : Mat n × Mat n → V} (hK : ContDiffOn ℝ ∞ K (Dm n)) :
    ContDiffOn ℝ ∞ (Hw w K) (Dm n) := by
  induction w with
  | nil => simpa using hK
  | cons p w ih => rw [Hw_cons]; exact Ldp_contDiffOn _ ih

theorem toL_congr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)]
    (μ : Measure (G n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : toL μ f = toL μ h := by
  have : (fun y : G n => f y.val) = fun y => h y.val := funext fun y => e (GlobalTheory.CompanionTheory.KerUniq.val_mem y)
  by_cases hm : MemLp (fun y : G n => f y.val) 2 μ
  · exact (isRep_toL (isRep_congr e (toL_coe hm))).symm
  · have hm' : ¬ MemLp (fun y : G n => h y.val) 2 μ := this ▸ hm
    unfold toL
    rw [dif_neg hm, dif_neg hm']

theorem cvl_eq (hu : Unimod) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (φ : Mat n → ℂ) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) {x : Mat n} (hx : x ∈ GLs n) :
    cvl μ φ (toL μ f) x = ∫ z : G n, φ z.val • Hf f (z.val, x) ∂μ := by
  obtain ⟨h1, h2⟩ := hu n μ
  let u : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx
  have hu' : u.val = x := rfl
  let F : G n → V := fun z => φ (x * (z⁻¹ : G n).val) • f z.val
  have e1 : cvl μ φ (toL μ f) x = ∫ z, F z ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [toL_coe hf] with z hz
    simp only [F]
    rw [hz]
  have e2 : ∫ z, F z ∂μ = ∫ z, F (z⁻¹ * u) ∂μ := by
    rw [integral_inv_eq_self (fun z => F (z * u)) μ, integral_mul_right_eq_self F u]
  rw [e1, e2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have e3 : x * ((z⁻¹ * u)⁻¹ : G n).val = z.val := by
    have e4 : (z⁻¹ * u)⁻¹ = u⁻¹ * z := by group
    rw [e4, Units.val_mul, ← mul_assoc]
    have e5 : x * (u⁻¹ : G n).val = 1 := by rw [← hu']; exact Units.mul_inv u
    rw [e5, one_mul]
  show φ (x * ((z⁻¹ * u)⁻¹ : G n).val) • f (z⁻¹ * u).val = φ z.val • f (z.val⁻¹ * x)
  rw [e3]
  simp [hu', Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.QLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  apply Fin.ext
  simp [ePG]

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem two_true_eq (i t : ℕ) (b : Fin t) :
    two (stdSum (rfl : i + t = i + t)) ⟨true, b⟩ = Fin.natAdd i b := by
  apply Fin.ext
  simp

theorem two_false_eq (i t : ℕ) (a : Fin i) :
    two (stdSum (rfl : i + t = i + t)) ⟨false, a⟩ = Fin.castAdd t a := by
  apply Fin.ext
  simp

theorem levi_entry (n : ℕ) (g : GL (Fin n) k) (a b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (g : Matrix (Fin n) (Fin n) k) a b := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_col (n : ℕ) (g : GL (Fin n) k) (a : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_row (n : ℕ) (g : GL (Fin n) k) (b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc b) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last (n : ℕ) (g : GL (Fin n) k) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_mem_HPG (i t : ℕ) (q : Qp k i t) : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t := by
  show ((levi k (i + t) (q : GL (Fin (i + t)) k) : Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t)
  refine mem_parab_iff.2 ?_
  intro a c x y hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hx : ePG i t ⟨true, x⟩ = Fin.castSucc (Fin.natAdd i (x : Fin t)) := ePG_true_eq i t x
  rw [hx]
  induction (y : Fin (i + 1)) using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact levi_entry_last_col _ _ _
  | cast y =>
    rw [ePG_false_eq, levi_entry]
    have := mem_parab_iff.1 q.2 true false (x : Fin t) (y : Fin i) (by decide)
    rwa [two_true_eq, two_false_eq] at this

theorem pgProj_levi (i t : ℕ) (q : Qp k i t) (h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t) :
    pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) false : GL (Fin (i + 1)) k).val a b =
      ((levi k i (qBlocks k i t q).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b
    rw [leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨false, a⟩) (ePG i t ⟨false, b⟩) = _
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last, levi_entry_last]
      | cast b => rw [ePG_false_eq, levi_entry_last_row, levi_entry_last_row]
    | cast a =>
      rw [ePG_false_eq]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last_col, levi_entry_last_col]
      | cast b =>
        rw [ePG_false_eq, levi_entry, levi_entry]
        show _ = (leviProj k (two (stdSum (rfl : i + t = i + t))) q false : GL (Fin i) k).val a b
        rw [leviProj_apply, two_false_eq, two_false_eq]
  · apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) true : GL (Fin t) k).val a b =
      (leviProj k (two (stdSum (rfl : i + t = i + t))) q true : GL (Fin t) k).val a b
    rw [leviProj_apply, leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨true, a⟩) (ePG i t ⟨true, b⟩) = _
    rw [ePG_true_eq, ePG_true_eq, levi_entry, two_true_eq, two_true_eq]

end GlobalTheory.CompanionTheory.BZPsiPG.QLevi

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem levi_Qp_mem_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (q : Qp k i t) :
    ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t,
      pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) :=
  ⟨QLevi.levi_mem_HPG i t q, QLevi.pgProj_levi i t q _⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpanStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_span_inf_ideal_le_square_span : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n → x ∈ sqSpan n := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp | exact GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp | (intros; apply GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolicStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (g : Mir k (m + j)), g ∈ MirabolicParabolic k m j ↔ mirabolicProjection k (m + j) g ∈ parab k (two (stdSum (rfl : m + j = m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic | exact GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic | (intros; apply GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExactStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_phi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPhiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPhiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPhiMinus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExactStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_psi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPsiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPsiMinus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotentStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_of_simple_lowering_nilpotent : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → (j : ℕ) = i + 1 → (∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) → ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | exact GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | (intros; apply GlobalTheory.CompanionTheory.PresRho.natural_of_primitive <;> assumption)
end

