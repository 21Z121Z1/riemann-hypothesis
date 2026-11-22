import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParameters
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNonzeroIntertwiner
section
noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]

theorem avg_inner_map {T : W →L[ℂ] W} (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : W) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : W →ₗ[ℂ] W), hT⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y

theorem avg_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (KG ε) := by
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact hemb.isInducing.secondCountableTopology

theorem avg_continuous_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

def avgF (T : Mat n → (W →L[ℂ] W)) (S : Mat n → (Z →L[ℂ] Z)) (e : W) (f : Z) (w : W) (k : KG ε) : Z :=
  ⟪T (toMK k) e, w⟫_ℂ • S (toMK k) f

theorem avgF_continuous {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Continuous (avgF (ε := ε) T S e f w) := by
  have h1 : Continuous fun k : KG ε => T (toMK k) e :=
    (hT.2.2 e).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  have h2 : Continuous fun k : KG ε => S (toMK k) f :=
    (hS.2.2 f).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  exact (h1.inner continuous_const).smul h2

theorem avgF_integrable {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Integrable (avgF (ε := ε) T S e f w) (muK ε) := by
  have := avg_secondCountable ε
  exact integrableOn_univ.1 ((avgF_continuous hT hS e f w).continuousOn.integrableOn_compact isCompact_univ)

def avgMapL {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z) :
    W →ₗ[ℂ] Z where
  toFun w := ∫ k, avgF T S e f w k ∂(muK ε)
  map_add' x y := by
    rw [← integral_add (avgF_integrable hT hS e f x) (avgF_integrable hT hS e f y)]
    congr 1; funext k; simp [avgF, inner_add_right, add_smul]
  map_smul' c x := by
    rw [RingHom.id_apply, ← integral_smul]
    congr 1; funext k; simp [avgF, inner_smul_right, smul_smul]

theorem avgMapL_apply {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : avgMapL hT hS e f w = ∫ k, avgF T S e f w k ∂(muK ε) := rfl

theorem avgMapL_intertwines {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (g : KG ε) (w : W) : avgMapL hT hS e f (T (toMK g) w) = S (toMK g) (avgMapL hT hS e f w) := by
  rw [avgMapL_apply, avgMapL_apply, ← (S (toMK g)).integral_comp_comm (avgF_integrable hT hS e f w),
    ← integral_mul_left_eq_self _ g]
  congr 1; funext k
  have hm : toMK (g * k) = toMK g * toMK k := rfl
  simp only [avgF, hm, hT.1.2 _ g.2 _ k.2, hS.1.2 _ g.2 _ k.2, ContinuousLinearMap.comp_apply, map_smul]
  rw [avg_inner_map (hT.2.1 _ g.2)]

end

theorem tracePairing_nonzero_intertwiner : AvgMap := by
  intro n ε W _ _ _ T Z _ _ _ S Γ hT hS hne
  classical
  set b := stdOrthonormalBasis ℂ W
  set c := stdOrthonormalBasis ℂ Z
  let φ : Fin (Module.finrank ℂ Z) → Z →L[ℂ] ℂ := fun j =>
    LinearMap.toContinuousLinearMap ((innerₛₗ ℂ (c j)).comp Γ)
  have hφ : ∀ j u, φ j u = ⟪c j, Γ u⟫_ℂ := fun j u => rfl
  have hpt : ∀ i j (k : KG ε), φ j (avgF T S (b i) (c j) (b i) k) =
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
    intro i j k
    simp [avgF, hφ, map_smul, inner_conj_symm]
  have hint : ∀ i j, Integrable (fun k : KG ε =>
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ) (muK ε) := fun i j =>
    ((φ j).integrable_comp (avgF_integrable hT hS (b i) (c j) (b i))).congr
      (Filter.Eventually.of_forall fun k => hpt i j k)
  have key : ∀ i j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ =
      ∫ k, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ ∂(muK ε) := by
    intro i j
    rw [avgMapL_apply, ← hφ, ← (φ j).integral_comp_comm (avgF_integrable hT hS _ _ _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => hpt i j k)
  have hsum : ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) =
      ∑ i, ∑ j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ := by
    simp only [key]
    have hpw : ∀ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) =
        ∑ i, ∑ j, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
      intro k
      simp only [trK, LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ c, map_sum,
        Finset.sum_mul, Finset.mul_sum, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      exact Finset.sum_comm
    simp_rw [hpw]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
  rw [hsum] at hne
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  refine ⟨avgMapL hT hS (b i) (c j), fun h0 => hj ?_, fun k hk v => ?_⟩
  · rw [h0, LinearMap.zero_apply, map_zero, inner_zero_right]
  · have hk' : k ∈ Set.range (fun g : KG ε => toMK g) := by rw [Formalism.REAL.range_toMK]; exact hk
    obtain ⟨g, rfl⟩ := hk'
    exact avgMapL_intertwines hT hS (b i) (c j) g v

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionCuspidalOfRapidDecayHolomorphicTypeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionCuspidal_of_rapidDecay_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  first | exact @GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay | exact GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay | (intros; apply GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGeneratedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_ample_globally_generated : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 | exact GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 | (intros; apply GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CentComm

theorem commute_of_commute_separable_of_isAlgClosed {L : Type} [Field L] [IsAlgClosed L] {n : ℕ}
    {A g h : Matrix (Fin n) (Fin n) L} (hA : A.charpoly.Separable) (hg : Commute A g) (hh : Commute A h) :
    Commute g h := by
  set f := Matrix.toLin' A
  have hc : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' g) := hg.map Matrix.toLinAlgEquiv'
  have hfh : Commute f (Matrix.toLin' h) := hh.map Matrix.toLinAlgEquiv'
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤
      LinearMap.ker (Matrix.toLin' g * Matrix.toLin' h - Matrix.toLin' h * Matrix.toLin' g) := fun μ v hv => by
    have h1 : Module.finrank L (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hc]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have hs : ∀ w ∈ Module.End.maxGenEigenspace f μ, ∃ c : L, c • v = w := fun w hw => by
      have h2 : Module.finrank L (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨w, hw⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    obtain ⟨c, hc⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv)
    obtain ⟨d, hd⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfh μ hv)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ← hc, ← hd, map_smul,
      map_smul, ← hc, ← hd, smul_comm, sub_self]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h3
  exact Matrix.toLinAlgEquiv'.injective (by rw [map_mul, map_mul]; exact h3)

theorem commute_of_commute_separable {K : Type} [Field K] {n : ℕ} {A g h : Matrix (Fin n) (Fin n) K}
    (hA : A.charpoly.Separable) (hg : Commute A g) (hh : Commute A h) : Commute g h := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hA' : (A.map φ).charpoly.Separable := by
    rw [Matrix.charpoly_map]; exact hA.map
  have hg' : Commute (A.map φ) (g.map φ) := by
    unfold Commute SemiconjBy; rw [← Matrix.map_mul, ← Matrix.map_mul, hg.eq]
  have hh' : Commute (A.map φ) (h.map φ) := by
    unfold Commute SemiconjBy; rw [← Matrix.map_mul, ← Matrix.map_mul, hh.eq]
  have := commute_of_commute_separable_of_isAlgClosed hA' hg' hh'
  unfold Commute SemiconjBy at this ⊢
  rw [← Matrix.map_mul, ← Matrix.map_mul] at this
  exact Matrix.map_injective φ.injective this

end GlobalTheory.BCT.CentComm

namespace GlobalTheory.BCT

theorem centComm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y,
      a * b = b * a := by
  intro E _ _ _ _ n w y hy a ha b hb
  have ha' : a.1.val * y.1.val = y.1.val * a.1.val := congrArg (fun z : UL n w => z.1.val) ha
  have hb' : b.1.val * y.1.val = y.1.val * b.1.val := congrArg (fun z : UL n w => z.1.val) hb
  have := CentComm.commute_of_commute_separable hy ha'.symm hb'.symm
  exact Subtype.ext (Units.ext this.eq)

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MassTor

section Closed

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isCompact_closure_zpowers_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    IsCompact (closure (Subgroup.zpowers (t : G) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set T)) := by
  have hE : Topology.IsClosedEmbedding (Subtype.val : T → G) := hT.isClosedEmbedding_subtypeVal
  have h1 : (Subgroup.zpowers (t : G) : Set G) = Subtype.val '' (Subgroup.zpowers t : Set T) := by
    have := MonoidHom.map_zpowers T.subtype t
    rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, this]
  rw [h1, hE.closure_image_eq, ← hE.isEmbedding.isCompact_iff]

theorem cptPart_eq_map {T : Subgroup G} (hT : IsClosed (T : Set G)) :
    cptPart T = (Subgroup.closure {t : T | IsCompact (closure (Subgroup.zpowers t : Set T))}).map T.subtype := by
  rw [MonoidHom.map_closure]
  unfold cptPart
  congr 1
  ext g
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, (isCompact_closure_zpowers_iff hT ⟨g, hg⟩).1 hc, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, (isCompact_closure_zpowers_iff hT t).2 ht⟩

theorem cptPart_le (T : Subgroup G) : cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem mem_cptPart_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    (t : G) ∈ cptPart T ↔ t ∈ Subgroup.closure {s : T | IsCompact (closure (Subgroup.zpowers s : Set T))} := by
  rw [cptPart_eq_map hT, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, h⟩
    rwa [show s = t from Subtype.ext h] at hs
  · intro h
    exact ⟨t, h, rfl⟩

end Closed

theorem mem_closure_cpt_iff {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] (e : A ≃ₜ* B)
    (a : A) :
    a ∈ Subgroup.closure {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} ↔
      e a ∈ Subgroup.closure {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
  have key : ∀ s : A, IsCompact (closure (Subgroup.zpowers s : Set A)) ↔
      IsCompact (closure (Subgroup.zpowers (e s) : Set B)) := by
    intro s
    have h1 : (Subgroup.zpowers (e s) : Set B) = e '' (Subgroup.zpowers s : Set A) := by
      have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom s
      have h := congrArg (fun H : Subgroup B => (H : Set B)) this
      rw [Subgroup.coe_map] at h
      exact h.symm
    rw [h1]
    have h2 := e.toHomeomorph.image_closure (Subgroup.zpowers s : Set A)
    have h3 := e.toHomeomorph.isCompact_image (s := closure (Subgroup.zpowers s : Set A))
    rw [show (⇑e.toHomeomorph : A → B) = ⇑e from rfl] at h2 h3
    rw [← h2, h3]
  have himg : e.toMulEquiv.toMonoidHom '' {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} =
      {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
    ext b
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (key s).1 hs
    · intro hb
      refine ⟨e.symm b, (key _).2 ?_, ?_⟩
      · simpa using hb
      · exact e.apply_symm_apply b
  have hmap := MonoidHom.map_closure e.toMulEquiv.toMonoidHom
    {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))}
  rw [himg] at hmap
  rw [← hmap, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    have : x = a := e.injective h
    rwa [← this]

theorem card_doubleCoset_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (H K : Subgroup A) (H' K' : Subgroup B)
    (hH : ∀ a, a ∈ H ↔ e a ∈ H') (hK : ∀ a, a ∈ K ↔ e a ∈ K') :
    Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) =
      Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  apply Nat.card_congr
  refine Quotient.congr e.toEquiv fun x y => ?_
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, (hH a).1 ha, e b, (hK b).1 hb, by simp [map_mul]⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨e.symm a, (hH _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] at h
    simp [map_mul, h]

theorem isClosed_twCent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G)
    (hθ : Continuous θ) (δ : G) : IsClosed (twCent θ δ : Set G) :=
  isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)

theorem mass_eq_of_equiv (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G')
    (δ : G) (δ' : G') (hT : IsClosed (twCent θ δ : Set G)) (hT' : IsClosed (twCent θ' δ' : Set G'))
    (e : twCent θ δ ≃ₜ* twCent θ' δ')
    (hΓ : ∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') :
    mass θ Γ δ = mass θ' Γ' δ' := by
  have hC : ∀ t : twCent θ δ, (t : G) ∈ cptPart (twCent θ δ) ↔ ((e t : twCent θ' δ') : G') ∈ cptPart (twCent θ' δ') :=
    fun t => by rw [mem_cptPart_iff hT, mem_cptPart_iff hT', mem_closure_cpt_iff e]
  have hmem : ∀ t : twCent θ δ, (t : G) ∈ Γ ⊓ cptPart (twCent θ δ) ↔
      ((e t : twCent θ' δ') : G') ∈ Γ' ⊓ cptPart (twCent θ' δ') := fun t => by
    simp only [Subgroup.mem_inf]
    rw [hΓ t, hC t]
  let f : (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) ≃ (Γ' ⊓ cptPart (twCent θ' δ') : Subgroup G') :=
    { toFun := fun g => ⟨(e ⟨g, cptPart_le _ g.2.2⟩ : G'), (hmem _).1 g.2⟩
      invFun := fun g' => ⟨(e.symm ⟨g', cptPart_le _ g'.2.2⟩ : G),
        (hmem (e.symm ⟨g', cptPart_le _ g'.2.2⟩)).2 (by rw [e.apply_symm_apply]; exact g'.2)⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g' => by ext; simp }
  unfold mass
  rw [card_doubleCoset_congr e.toMulEquiv _ _ (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf _)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hΓ a)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hC a), Nat.card_congr f]

end GlobalTheory.MassTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
section
open Filter GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwOrbGood

theorem avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold GlobalTheory.BCT.avg
  rw [h, Subgroup.index_top]
  have : (∑ᶠ q : H ⧸ (⊤ : Subgroup H), (fun _ : H => c) q.out) = c := by
    rw [finsum_eq_single (fun q : H ⧸ (⊤ : Subgroup H) => (fun _ : H => c) q.out) (QuotientGroup.mk 1)
      (fun q hq => absurd (by induction q using QuotientGroup.induction_on with | H a => exact QuotientGroup.eq.2 (Subgroup.mem_top _)) hq)]
  rw [this]; simp

theorem summand_goodplace : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  intro H _ _ _ KH δ hδ hc hg x
  split_ifs with hx
  · obtain ⟨t, ht, k, hk, rfl⟩ := hx
    have e : t * k = t * 1 * k := by group
    rw [e, GlobalTheory.TwOrbConj.summand_rep _ _ _ _ _ ht hk]
    unfold GlobalTheory.TwOrbConj.summand
    have hmap : KH.map (MulAut.conj (1 : H)).toMonoidHom = KH := GlobalTheory.TwOrbConj.map_conj_self KH KH.one_mem
    have hcT : cptPart (twCent (MonoidHom.id H) δ) ≤ twCent (MonoidHom.id H) δ := by
      unfold GlobalTheory.BCT.cptPart
      rw [Subgroup.closure_le]
      intro y hy; exact hy.1
    have hrel : (twCent (MonoidHom.id H) δ ⊓ KH.map (MulAut.conj (1 : H)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) δ)) = 1 := by
      rw [hmap, Subgroup.relIndex_eq_one]
      exact le_inf hcT hc
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((1 * (k : H))⁻¹ * δ * (MonoidHom.id H) (1 * (k : H))))
        = fun _ => 1 := by
      funext k
      rw [Set.indicator_of_mem]
      · rfl
      · simp only [one_mul, MonoidHom.id_apply]
        exact KH.mul_mem (KH.mul_mem (KH.inv_mem k.2) hδ) k.2
    rw [hrel, hfun, avg_const]; simp
  · unfold GlobalTheory.TwOrbConj.summand
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((x * (k : H))⁻¹ * δ * (MonoidHom.id H) (x * (k : H))))
        = fun _ => 0 := by
      funext k
      rw [Set.indicator_of_notMem]
      intro hm
      simp only [MonoidHom.id_apply] at hm
      obtain ⟨t, ht, htk⟩ := hg (x * k) hm
      apply hx
      refine ⟨t, ht, t⁻¹ * (x * k) * (k : H)⁻¹, KH.mul_mem htk (KH.inv_mem k.2), by group⟩
    rw [hfun, avg_const]; simp

end GlobalTheory.TwOrbGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwTrUnit

theorem trace_eq_zero_of_finrank_eq_zero (W : Type) [AddCommGroup W] [Module ℂ W] (h : Module.finrank ℂ W = 0)
    (L : W →ₗ[ℂ] W) : LinearMap.trace ℂ W L = 0 := by
  by_cases hW : Module.Finite ℂ W
  · haveI : Subsingleton W := Module.finrank_zero_iff.1 h
    rw [show L = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  · unfold LinearMap.trace
    rw [dif_neg]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem isHecke_indicator {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hK : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) :
    IsHecke K' ((K' : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K' : Set G) := K'.isClosed_of_isOpen ho
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset hcl hle
  refine ⟨HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · have : k * x ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_left hk
    simp only [Set.indicator_apply, this, Pi.one_apply]
  · have : x * k ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_right hk
    simp only [Set.indicator_apply, this, Pi.one_apply]

theorem twTr_indicator {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) : twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) := by
  obtain ⟨x₀, hx₀, hL⟩ := GlobalTheory.TwTrLin.levOp_unit ρ K K'
  have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).1 hv x₀ hx₀
  have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [hL, LinearMap.smul_apply, hfx v hv]
    exact Submodule.smul_mem _ _ hv
  rw [GlobalTheory.TwTrLin.twTr_eq _ _ _ _ _ hm]
  have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext x
    simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
  rw [hr, map_smul, GlobalTheory.TwTrLin.trace_id_eq_finrank, smul_eq_mul]

theorem twTr_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id (UL n w)) (KL n w) K' → ∀ σ : SmIrr (UL n w), IsHecke K' ((K' : Set (UL n w)).indicator 1) ∧ K'.relIndex (KL n w) ≠ 0 ∧ twTr σ.ρ (KL n w) K' ((K' : Set (UL n w)).indicator 1) LinearMap.id = ((K'.relIndex (KL n w) : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed σ.ρ K') : ℂ) ∧ (Module.finrank ℂ (fixed σ.ρ K') = 0 → ∀ g, twTr σ.ρ (KL n w) K' g LinearMap.id = 0) := by
  intro E _ _ _ n w K' hlev σ
  have hKc := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨isHecke_indicator hKc hlev.1 hlev.2.1, GlobalTheory.TwTrLin.relIndex_ne_zero_of_isOpen hKc hlev.1,
    twTr_indicator _ _ _, fun h g => ?_⟩
  unfold twTr
  split_ifs with hm
  · exact trace_eq_zero_of_finrank_eq_zero _ h _
  · rfl

end GlobalTheory.TwTrUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParametersStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  first | exact @GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero | exact GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero | (intros; apply GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMInfinityComponentGlobalUnit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem inf_mu_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ v : InfinitePlace E, (v.embedding (k : E) / (‖v.embedding (k : E)‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ e hμ k
  have h1 : μ.inf k = chiInf μ (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)) := by
    rw [chiInf, MonoidHom.comp_apply, GlobalTheory.CuspRep.NormTriv.infId_pInf]
    change μ.1 (Formalism.L2.Host.infDiag k) = _
    rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply]
    rfl
  rw [h1, hμ.2.2.2.2]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)).1 v = v.embedding (k : E) :=
    GlobalTheory.CuspRep.pInf_algebraMap (k : E) v
  rw [this]

end GlobalTheory.BCT
end

