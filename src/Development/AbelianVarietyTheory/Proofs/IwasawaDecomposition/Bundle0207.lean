import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeSevenModSixteenGood
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeThreeModEightGood
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSectionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_square_polarisation_sections : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type) (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  first | exact @GlobalTheory.SquarePolCover.exists_cover | exact GlobalTheory.SquarePolCover.exists_cover | (intros; apply GlobalTheory.SquarePolCover.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeCharStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.IsUnitary → ∃ c, ChrEq c χ := by
  first | exact @GlobalTheory.CharTransport.exists_chrEq | exact GlobalTheory.CharTransport.exists_chrEq | (intros; apply GlobalTheory.CharTransport.exists_chrEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdelesStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), 1 ≤ M → IsHermND σ J → μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E), IsFibreFamily μ (fun X => qR (Ainf F) σ J (X 0)) id Set.univ ν {c : Ainf F | ∀ w, c w ≠ 0} fib := by
  first | exact @GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf | exact GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf | (intros; apply GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImNeZeroOfTotallyComplex
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_im_ne_zero_of_totallyComplex {K : Type} [Field K] [IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  exact Complex.conj_eq_iff_im.2 (h a)

theorem lin_single_cpt {K : Type} [Field K] (σ : K →+* ℂ) {d : ℕ} {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (e : (Fin d → K) ≃ₗ[K] V) (j : V →ₛₗ[σ] W) (x : Fin d → K) :
    lin (fun k => j (e (Pi.single k 1))) (cpt σ x) = j (e x) := by
  rw [lin_apply]
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum, map_smulₛₗ, cpt]

theorem rows_eq_rows_level : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.RRTie cr → (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ ∀ F, ‖M.eR F‖ = Real.sqrt (X.nP true) * ‖F‖ := by
  intro D Bs A X fc s R cr M eV hX hT
  obtain ⟨L, hT⟩ := hT
  have hn : 0 < X.nP true := hX.pos.2.2 true
  let g := lin (fun k => D.jEE (R.eRR (Pi.single k 1)))
  have hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x) := lin_single_cpt _ R.eRR D.jEE
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩
  have key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z) := by
    intro z
    rw [← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, M.eR_eq]
    congr 2
    funext i
    by_cases h : i = k <;> simp [cpt, h]
  have hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z := by
    intro z
    funext i
    cases s <;> simp [cjv, cj]
  refine ⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key, ← hX.h2.2.2]
    exact ⟨_, rfl⟩
  · rw [← hX.h2.2.2] at he
    obtain ⟨z, rfl⟩ := he
    exact ⟨g (cjv s z), by rw [key, hcc]⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key]
    have hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _) :=
      DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))
    have hcj : Continuous (cj s) := by
      cases s
      · exact continuous_id
      · exact Complex.continuous_conj
    have hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z :=
      continuous_pi fun i => hcj.comp (continuous_apply i)
    have h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖ :=
      ((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm
    have h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖ :=
      continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    have hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
      funext i
      simp [cjv, cpt, R.twist]
    have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) := by
      simp [CxData.XE, rowXE, rowFrame, spliceFrame]
    have hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1) :=
      li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)
    have hm := majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x
    rw [lin_basis] at hm
    rw [hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K,
      ← Real.sqrt_mul hn.le]
    erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re =
      (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]
    rw [mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasure
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_isProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), Conv b mi mv → ∃ ν, IsProd b ν mi mv := by
  intro F E _ _ _ _ _ d b n M mi mv hc
  obtain ⟨hi, hv, hs⟩ := hc
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : Countable (𝓞 F) := Countable.of_equiv _ (RingOfIntegers.basis F).equivFun.symm.toEquiv
  haveI : Countable (Ideal (𝓞 F)) := by
    have hsurj : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) :=
      fun I => (IsNoetherian.noetherian I)
    exact hsurj.countable
  haveI : Countable (HeightOneSpectrum (𝓞 F)) :=
    Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun _ _ h => HeightOneSpectrum.ext h)
  obtain ⟨hint, -⟩ := GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d b
  obtain ⟨hemb, hrange, -, -⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  have hlat : ∀ v, (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
    intro v
    ext Y
    rw [mem_latV_iff]
    simp
  have hcpt : ∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hint v).1
  have hmeas : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => (hint v).2.measurableSet
  have hsi : SigmaFinite mi := inferInstance
  have hsv : ∀ v, SigmaFinite (mv v) := fun v => by
    haveI := hv v
    infer_instance
  obtain ⟨ν, hν0, hν⟩ := GlobalTheory.T.exists_restricted_product_measure_countable (HeightOneSpectrum (𝓞 F)) _ _ (fun v => latV b v) mi mv hsi hsv hmeas
    (fun v => by haveI := hv v; exact (hcpt v).measure_lt_top.ne) hs
  set e := (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) with he
  have hmap : (ν.comap e).map e = ν := by
    rw [hemb.map_comap, hrange]
    exact Measure.restrict_eq_self_of_ae_mem hν0
  refine ⟨ν.comap e, ⟨hi, hv, hs⟩, fun S fi fv hfi hfv => ?_⟩
  have h := hν S fi fv hfi hfv
  rw [← hmap, hemb.restrict_map, hemb.lintegral_map] at h
  exact h

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElementStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_components_adelic_unitary_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  first | exact @GlobalTheory.GaugeEx.LocComp.exists_local_components | exact GlobalTheory.GaugeEx.LocComp.exists_local_components | (intros; apply GlobalTheory.GaugeEx.LocComp.exists_local_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowerEmbF
section
noncomputable section

namespace GlobalTheory.Mem.Col2.KerRat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem sum_cover {K M G D G' D' : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] [MulAction G D] [Group G']
    [MulAction G' D'] [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient G' D')]
    (π : D → D') (hs : Function.Surjective π) (h1 : ∀ (g : G) d, ∃ g' : G', π (g • d) = g' • π d)
    (h2 : ∀ (g' : G') d e, g' • π d = π e → ∃ g : G, g • d = e)
    (h3 : ∀ d, Nat.card (MulAction.stabilizer G d) = Nat.card (MulAction.stabilizer G' (π d)))
    (r : MulAction.orbitRel.Quotient G D → D) (hr : ∀ q, Quotient.mk (MulAction.orbitRel G D) (r q) = q)
    (r' : MulAction.orbitRel.Quotient G' D' → D') (hr' : ∀ q, Quotient.mk (MulAction.orbitRel G' D') (r' q) = q)
    (f : D' → M) (hf : ∀ (g' : G') d, f (g' • d) = f d) :
    ∑ q, ((Nat.card (MulAction.stabilizer G (r q)) : ℕ) : K)⁻¹ • f (π (r q)) =
      ∑ q, ((Nat.card (MulAction.stabilizer G' (r' q)) : ℕ) : K)⁻¹ • f (r' q) := by
  refine Fintype.sum_bijective (fun q => Quotient.mk (MulAction.orbitRel G' D') (π (r q))) ⟨fun q q' h => ?_, fun q' => ?_⟩ _ _
    fun q => ?_
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q') = π (r q) := Quotient.exact h
    obtain ⟨g, hg⟩ := h2 g' _ _ hg
    rw [← hr q, ← hr q']
    exact Quotient.sound ⟨g, hg⟩
  · obtain ⟨d, hd⟩ := hs (r' q')
    refine ⟨Quotient.mk _ d, ?_⟩
    obtain ⟨g, hg⟩ : ∃ g : G, g • d = r (Quotient.mk _ d) := Quotient.exact (hr (Quotient.mk _ d))
    obtain ⟨g', hg'⟩ := h1 g d
    rw [← hr' q', ← hd]
    exact Quotient.sound ⟨g', by rw [← hg, hg']⟩
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q) = r' (Quotient.mk _ (π (r q))) := Quotient.exact (hr' (Quotient.mk _ (π (r q))))
    rw [← hg, hf, h3, Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := G') (a := π (r q)) (b := g' • π (r q)) (g := g') rfl).toEquiv]

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  (I : ChainIn E K ι R) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R) (hI : I.Ok)

abbrev PtKer : Type := ∀ i b b', (I.S i).D b → (I.S (i + 1)).D b' → (VV K (lamT hc i) →ₗ[K] VV K (lamT hc (i + 1)))

abbrev ev (i : ℕ) : VV K (lamT hc i) →ₛₗ[σ] (Fr emb σ (R.N i) → ℂ) :=
  evV emb (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) E) (lamT hc i) σ

variable {I hc} (k : PtKer I hc)

def EqTarget (i : ℕ) : Prop := ∀ b b' (g' : (I.S (i + 1)).G b') d d',
  k i b b' d (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' ∘ₗ k i b b' d d'

def ReadsAt (i : ℕ) : Prop := ∀ c c' F, (I.chain emb σ hI hc).Kmap i c c' (ev emb σ hc i F) =
  ev emb σ hc (i + 1) (k i c.1 c'.1 ((I.S i).rep c) ((I.S (i + 1)).rep c') F)

def stepPt (i : ℕ) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β) (d' : (I.S (i + 1)).D b') : VV K (lamT hc (i + 1)) :=
  letI := I.clFin hI i
  ∑ c : (I.S i).Cl, ((Nat.card ((I.S i).Stab c) : ℕ) : K)⁻¹ • k i c.1 b' ((I.S i).rep c) d' (x c)

def colPt (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (j : ℕ) : ∀ b, (I.S j).D b → VV K (lamT hc j) :=
  Nat.rec (motive := fun j => ∀ b, (I.S j).D b → VV K (lamT hc j)) φ
    (fun j ψ => stepPt hI k j fun c => ψ c.1 ((I.S j).rep c)) j

variable {emb k}

theorem stepPt_smul {i : ℕ} (h : EqTarget emb k i) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β)
    (g' : (I.S (i + 1)).G b') (d' : (I.S (i + 1)).D b') :
    stepPt hI k i x b' (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' (stepPt hI k i x b' d') := by
  unfold stepPt
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h, map_smul]
  rfl

theorem colPt_smul (h : ∀ i, i < R.m → EqTarget emb k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (h0 : 0 < j) (hj : j ≤ R.m)
    (b : (I.S j).β) (g : (I.S j).G b) (d : (I.S j).D b) :
    colPt hI k φ j b (g • d) = (I.S j).rho emb (lamT hc j) b g (colPt hI k φ j b d) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact stepPt_smul hI (h i (by omega)) _ b g d

variable {σ hI}

theorem K_ev {i : ℕ} (h : ReadsAt emb σ hI k i) (x : (I.S i).Cl → VV K (lamT hc i)) :
    (I.chain emb σ hI hc).K i (fun c => ev emb σ hc i (x c)) =
      fun c' => ev emb σ hc (i + 1) (stepPt hI k i x c'.1 ((I.S (i + 1)).rep c')) := by
  funext c'
  unfold stepPt
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.map_smulₛₗ, map_inv₀, map_natCast, ← h]
  rfl

theorem chain_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (hj : j ≤ R.m) :
    letI := (I.chain emb σ hI hc).clsFin
    Formalism.ThetaLiftIndependence.chainOpM (I.chain emb σ hI hc).wt (I.chain emb σ hI hc).Kmap j (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) =
      fun c => ev emb σ hc j (colPt hI k φ j c.1 ((I.S j).rep c)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine Eq.trans ?_ (K_ev (h j (by omega)) fun c => colPt hI k φ j c.1 ((I.S j).rep c))
    rw [← ih (by omega)]
    rfl

theorem exists_K_embF {i : ℕ} (h : ReadsAt emb σ hI k i) (h' : EqTarget emb k i) (hF : ((I.S i).fam emb (lamT hc i)).Ok)
    (hF' : ((I.S (i + 1)).fam emb (lamT hc (i + 1))).Ok) (x : (I.S i).FormsK emb (lamT hc i) hF) :
    ∃ y, (I.S (i + 1)).embF emb σ (lamT hc (i + 1)) hF' y = (I.chain emb σ hI hc).K i ((I.S i).embF emb σ (lamT hc i) hF x) :=
  ⟨⟨fun c' => stepPt hI k i x.1 c'.1 ((I.S (i + 1)).rep c'), fun c' g =>
    (stepPt_smul hI h' x.1 c'.1 g.1 _).symm.trans (congrArg (stepPt hI k i x.1 c'.1) g.2)⟩, (K_ev h x.1).symm⟩

variable (Q : PerIn I) (hQ : Q.Ok)

theorem lower_ev (x : (I.S R.m).Cl → VV K (lamT hc R.m)) (c : Q.S'.Cl) :
    (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz fun c => ev emb σ hc R.m (x c)) c =
      evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
          ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x (Q.tilC c)))) := by
  show fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x (Q.tilC c)))))) = _
  rw [← LvT.BuiltChain.evV_rho, LvT.BuiltChain.polOf_evV, LvT.BuiltChain.br_map]
  rfl

theorem exists_lower_embF (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ))
    (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ)) (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) :
    ∃ y, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, funext fun c => (lower_ev Q hQ x.1 c).symm⟩
  have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
      (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
  have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
    have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
    rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    exact h3
  show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
  rw [← LvT.BuiltChain.brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
    (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
    (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
  exact congrArg B h2

theorem ptilCol_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (h' : ∀ i, i < R.m → EqTarget emb k i)
    (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (F : Q.Mt emb σ) (y : Q.S'.Cl → VV K Q.sgT)
    (hy : ∀ c, Q.rd emb σ F c = MvPolynomial.map σ (y c).1) :
    (Q.per emb σ hI hQ hc).PtilCol (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) F = letI := Q.clFin hQ
      σ (∑ c : Q.S'.Cl, ((Nat.card (Q.S'.Stab c) : ℕ) : K)⁻¹ • pairBK Q.sgT
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) (colPt hI k φ R.m Q.b0 (Q.tilPt c))) (y c)) := by
  unfold PeriodMap.PtilCol PeriodMap.Ptil ColumnChain.col
  rw [chain_ev h φ le_rfl]
  have e := funext (lower_ev (σ := σ) (emb := emb) (hI := hI) Q hQ fun c => colPt hI k φ R.m c.1 ((I.S R.m).rep c))
  refine (congrArg (fun z => (Q.per emb σ hI hQ hc).period z F) e).trans ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  have e2 := colPt_smul hI h' φ (lt_of_lt_of_le (by norm_num) R.two_le_m) le_rfl Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
    ((I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.tilPt c)))
  rw [GStep.mv_smul] at e2
  rw [pairBK_apply, PeriodOnStep.map_pairB, ← hy, ← PeriodOnStep.polOf_evV σ emb, e2]
  rfl

end GlobalTheory.Mem.Col2.KerRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyRealStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, IsCharAF F ψ := by
  first | exact @GlobalTheory.GaugeEx.CharZero.exists_isCharAF | exact GlobalTheory.GaugeEx.CharZero.exists_isCharAF | (intros; apply GlobalTheory.GaugeEx.CharZero.exists_isCharAF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeSevenModSixteenGoodStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_seven_mod_sixteen_good : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q % 8 = 3 → Real.sqrt (GlobalTheoryTheory.X1 x eps) < q → (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps → ∃ d : ℕ, d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧ GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧ (∀ i k : Fin 2, GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d)) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧ BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
  first | exact @GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds | exact GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds | (intros; apply GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeThreeModEightGoodStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_three_mod_eight_good : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q : ℕ, q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < q ∧ (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧ ∀ d : ℕ, d.Prime → d % 4 = 3 → q ≠ d → GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir q) (8 * q * d) ∧ GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧ BoundsAtX x eps C (GlobalTheoryTheory.psDir q) (8 * q * d) := by
  first | exact @GlobalTheory.ChoiceOfModulus.exists_prime_good_bounds | exact GlobalTheory.ChoiceOfModulus.exists_prime_good_bounds | (intros; apply GlobalTheory.ChoiceOfModulus.exists_prime_good_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueFieldStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  first | exact @GlobalTheory.TameTau.tameChar_of_prime_residue | exact GlobalTheory.TameTau.tameChar_of_prime_residue | (intros; apply GlobalTheory.TameTau.tameChar_of_prime_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_section_compatible_square_thickening : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  first | exact @GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | exact GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | (intros; apply GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq <;> assumption)
end

