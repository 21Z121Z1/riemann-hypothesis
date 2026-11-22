import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftRelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      relDim (segreLift ι F W) = relDim W

theorem SegreLiftRelDim.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

example (h : SegreLiftRelDim.Statement) := h ℚ Unit (fun _ => Fin 2) ⊥ SegreLiftRelDim.hyps

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def ChartSecGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
      (∀ j, η j ∈ secOver S y β) →
      (GeneratesOver S y β η ↔
        ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
          (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (Set.range η) : Set Ω) =
            chartSecOver S y k₀ e β I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def DegEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)),
      Kleiman.IsSubvar x pp 1 → NumbersDVR.IsMultiProjPrime W → mIdealOver k (graphVec x s) ≤ W →
      W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp →
      NumbersDVR.intNum k W ![graphDeg n] = Kleiman.interNum pp ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveComap.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ e : ℕ,
        (relDim W = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
          Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveLift.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (e : ℕ), Kleiman.IsSubvar x pp e →
      ∃ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W ∧
        mIdealOver k (graphVec x s) ≤ W ∧ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeBaseComap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem isMultiProjPrime_baseComap (F : Type) [Field F] {K : Type} [DecidableEq K] {ι : K → Type} (k₀ : K)
    {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {W : Ideal (NumbersDVR.MRing ι F)} (hW : NumbersDVR.IsMultiProjPrime W) :
    NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) := by
  refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := fun _ : Unit => k₀)
    (g := fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) (fun _ => rfl)
    (fun _ _ _ => Subsingleton.elim _ _) ?_ ?_ hW
  · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, EmbeddingLike.apply_eq_iff_eq] at h
    rw [h]
  · rintro ⟨k, i⟩ ⟨⟨⟩, hk⟩
    obtain rfl : k₀ = k := hk
    exact ⟨⟨(), e i⟩, by simp⟩

theorem mIdealOver_le_baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {W : Ideal (NumbersDVR.MRing ι F)}
    (hW : mIdealOver F y ≤ W) : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W := by
  subst hx
  intro f hf
  rw [baseComap, Ideal.mem_comap]
  apply hW
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

theorem ModelCurves.proof (hdim : ModelCurvesDim.Statement) (hlift : ModelCurvesLift.Statement) :
    ModelCurves.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap F k₀ e hW,
    mIdealOver_le_baseComap F y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim F K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift F K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim F K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MConeMapOverBaseRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

universe u w

section Scale

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ} {y : Fin (N + 1) → K'}

def scaleBundle (P : Kleiman.LineBundle k y) (μ : K') (hμ : μ ≠ 0) : Kleiman.LineBundle k y where
  sub I := Submodule.span (Kleiman.chartRing k y I) {μ} * P.sub I
  mono I J h z hz := by
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact Submodule.mem_span_singleton_mul.mpr ⟨w, P.mono I J h w hw, rfl⟩
  mem_iff I J h z := by
    simp only [Submodule.mem_span_singleton_mul]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, haw⟩ := (P.mem_iff I J h w).mp hw
      refine ⟨a, ha, (a : K') • w, haw, ?_⟩
      simp only [smul_eq_mul]; ring
    · rintro ⟨a, ha, w, hw, hwz⟩
      refine ⟨μ⁻¹ * z, (P.mem_iff I J h _).mpr ⟨a, ha, ?_⟩, by field_simp⟩
      rw [smul_eq_mul] at hwz ⊢
      rw [show (a : K') * (μ⁻¹ * z) = w by
        rw [mul_left_comm, ← hwz, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]]
      exact hw
  fg I := (Submodule.fg_span_singleton μ).mul (P.fg I)
  invertible I := by
    obtain ⟨M, hM⟩ := P.invertible I
    refine ⟨Submodule.span (Kleiman.chartRing k y I) {μ⁻¹} * M, ?_⟩
    rw [mul_mul_mul_comm, hM, Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hμ,
      mul_one, ← Submodule.one_eq_span]

theorem restrictData_scale {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {Q : Kleiman.SubSystem k x Ω} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {P : Kleiman.LineBundle k y} {r : Ω → K'}
    (hr : Kleiman.RestrictData Q hxy P.toSubSystem r) (μ : K') (hμ : μ ≠ 0) :
    Kleiman.RestrictData Q hxy (scaleBundle P μ hμ).toSubSystem (fun q => μ * r q) where
  mem I q hq := Submodule.mem_span_singleton_mul.mpr ⟨r q, hr.mem I q hq, rfl⟩
  add I q hq q' hq' := by simp only [hr.add I q hq q' hq', mul_add]
  smul I q hq f s e hs hf hse := by simp only [hr.smul I q hq f s e hs hf hse]; ring
  span I := by
    change _ = Submodule.span _ {μ} * P.sub I
    rw [← hr.span I, Submodule.span_mul_span, Set.singleton_mul, Set.image_image]

end Scale

section GraphEq

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N m : ℕ}

abbrev baseRename : Kleiman.Poly k N →ₐ[k] MvPolynomial (Σ c, graphIdx N m c) k :=
  rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)

theorem mConeMapOver_baseRename (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {g : Kleiman.Poly k N} {e : ℕ}
    (hg : g.IsHomogeneous e) :
    mConeMapOver k (graphVec x s) (baseRename g) = C (aeval x g) * X baseBlock ^ e := by
  have h1 := DFunLike.congr_fun (mConeMapOver_graph_comp_base (S := k) x s) g
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [h1, Kleiman.cone_of_isHomogeneous x hg, AlgHom.restrictScalars_apply, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq]

theorem mConeMapOver_graphEq (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m) :
    mConeMapOver k (graphVec x s) (X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f) =
      C (s b * aeval x h - s l * aeval x f) * (X (Sum.inr ()) * X baseBlock ^ e) := by
  rw [map_sub, map_mul, map_mul, mConeMapOver_baseRename x s hh, mConeMapOver_baseRename x s hf]
  simp only [mConeMapOver, aeval_X, graphVec_inr, map_sub, map_mul]
  ring

theorem graphEq_of_le {K' : Type} [Field K'] [Algebra k K'] {x : Fin (N + 1) → Ω} {s : Fin m → Ω}
    {x' : Fin (N + 1) → K'} {s' : Fin m → K'}
    (hle : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s')) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m)
    (hx : s b * aeval x h = s l * aeval x f) : s' b * aeval x' h = s' l * aeval x' f := by
  have hmem : X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f ∈
      mIdealOver k (graphVec x s) := by
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    rw [mConeMapOver_graphEq x s hf hh, hx, sub_self, map_zero, zero_mul]
  have h0 := hle hmem
  change _ ∈ RingHom.ker _ at h0
  rw [RingHom.mem_ker] at h0
  change mConeMapOver k (graphVec x' s') _ = 0 at h0
  rw [mConeMapOver_graphEq x' s' hf hh, mul_eq_zero, C_eq_zero, sub_eq_zero] at h0
  exact h0.resolve_right (mul_ne_zero (X_ne_zero _) (pow_ne_zero _ (X_ne_zero _)))

end GraphEq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Points

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

theorem chartRingOver_oneBlock (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (hi : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← TranslateEq.chartRing.equiv S x hi]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Points

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem CycleSplit.Small.exists_residue {S : Type u} [CommRing S] {R : Type w} [CommRing R] [Algebra S R]
    (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type w) (_ : Field K) (_ : Algebra S K) (ψ : R →ₐ[S] K), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom S (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ S P), ?_⟩
  ext a
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
    ← map_zero (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))),
    (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem CycleSplit.Small.proof (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hPt : CycleSplit.PointSecs.Statement.{u, w}) : CycleSplit.Small.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M 𝔪 _ pp hpp hhom hle _ hdim
  by_cases hrel : ∃ j, (X j : Poly S N) ∉ pp
  swap
  · push Not at hrel
    exact Eventually.of_forall fun c => by
      rw [interSum_one, restrLen_of_irrelevant _ hrel, restrLen_of_irrelevant _ hrel, sub_zero]
  obtain ⟨j, hj⟩ := hrel
  have hxj : x j ≠ 0 := fun h0 =>
    hj (hle ((mem_primeOf_of_isHomogeneous (S := S) x (isHomogeneous_X S j)).mpr (by rw [aeval_X, h0])))
  obtain ⟨hPprime, hPy⟩ := PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hxj hj

  have := hPprime
  obtain ⟨K', _, _, ψ, hψ⟩ := CycleSplit.Small.exists_residue (S := S) (chartPrime pp hxj)
  let y : Fin (N + 1) → K' := fun i => ψ (ratio hxj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i hyi hxi
    apply hyi
    have : ratio (S := S) hxj i = 0 := Subtype.ext (by simp [ratio, hxi])
    simp only [y, this, map_zero]
  have hpy : primeOf (S := S) y = pp := hPy K' ψ hψ
  have hy0 : y ≠ 0 := by
    intro h
    have h1 : ratio (S := S) hxj j = 1 := Subtype.ext (by simp [ratio, div_self hxj])
    have := congrFun h j
    simp only [y, h1, map_one, Pi.zero_apply] at this
    exact one_ne_zero this
  have hyrel : ∃ i, (X i : Poly S N) ∉ primeOf (S := S) y := ⟨j, hpy ▸ hj⟩
  have hydim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1 := hpy ▸ hdim

  have key : ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen pp (Q.toSubSystem.twist (twistSys S x (c : ℤ))) =
        ((Module.length S ((twistBundle S y 0).twist (twistSys S y 0)).secs).toNat : ℤ) := by
    intro Q
    obtain ⟨Q', r, hR⟩ := PrimeFiltration.Restrict.proof S Ω N x pp hpp hhom hle j hxj hj K' ψ hψ hxy Q
    have hRD : RestrictData Q.toSubSystem hxy Q'.toSubSystem r :=
      ⟨fun I => (hR I).1, fun I => (hR I).2.1, fun I => (hR I).2.2.1, fun I => (hR I).2.2.2⟩
    obtain ⟨c₀, hc₀⟩ := SurjectiveClosed.proof Extension.full.{u, w, w} IdealTwistFamily.proof
      (TildeVanish.proof SerreVanish.full.{u, w}) S Ω N x Q pp hhom
    filter_upwards [eventually_ge_atTop c₀.toNat] with c hc
    have hcc : c₀ ≤ (c : ℤ) := by omega
    unfold restrLen
    rw [QuotientH0Length.length_secs_eq _ _ (hc₀ c hcc),
      (hRQ S Ω N x pp hpp hhom hle j hxj hj K' ψ hψ hxy Q Q' r hRD c 0).some.length_eq,
      (CechZerothCohomologySections.proof.{u, w, w} S K' N y K' _ hy0).some.length_eq,
      hPt S K' N y hyrel hydim Q' (twistBundle S y 0) c 0]
  filter_upwards [key M, key (twistBundle S x 0)] with c h1 h2
  rw [interSum_one, h1, show (twistSys S x 0).twist (twistSys S x (c : ℤ)) =
    (twistBundle S x 0).toSubSystem.twist (twistSys S x (c : ℤ)) from rfl, h2, sub_self]

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenFibNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing blockWeight IsMultiHomog IsMultiProjPrime gradedPiece hilbFn intNum
  genFib)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

namespace GenFibNef

section Transport

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem isMultiHomog_map_iff (f : MRing ι F₁) (b : K → ℕ) :
    IsMultiHomog (map (e : F₁ →+* F₂) f) b ↔ IsMultiHomog f b := by
  unfold IsMultiHomog IsWeightedHomogeneous
  simp only [coeff_map, ne_eq, RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]

noncomputable def quotEquiv (P : Ideal (MRing ι F₁)) :
    (MRing ι F₁ ⧸ P) ≃+* (MRing ι F₂ ⧸ P.map (map (e : F₁ →+* F₂))) :=
  Ideal.quotientEquiv P _ (mapEquiv (Σ k, ι k) e) (by
    congr 1)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem quotEquiv_mk (P : Ideal (MRing ι F₁)) (f : MRing ι F₁) :
    quotEquiv e P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk _ (map (e : F₁ →+* F₂) f) := rfl

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem quotEquiv_smul (P : Ideal (MRing ι F₁)) (r : F₁) (x : MRing ι F₁ ⧸ P) :
    quotEquiv e P (r • x) = e r • quotEquiv e P x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h₁ : r • Ideal.Quotient.mk P f = Ideal.Quotient.mk P (C r * f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₁, ← map_smul, smul_eq_C_mul]
  have h₂ : e r • Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (map (e : F₁ →+* F₂) f) =
      Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (C (e r) * map (e : F₁ →+* F₂) f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₂, ← map_smul, smul_eq_C_mul]
  rw [h₁, quotEquiv_mk, quotEquiv_mk, h₂, map_mul, map_C]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem quotEquiv_mem_gradedPiece (P : Ideal (MRing ι F₁)) (n : K → ℕ) (x : MRing ι F₁ ⧸ P)
    (hx : x ∈ gradedPiece P n) : quotEquiv e P x ∈ gradedPiece (P.map (map (e : F₁ →+* F₂))) n := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨map (e : F₁ →+* F₂) f, ?_, rfl⟩
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  exact (isMultiHomog_map_iff e f n).2 hf

theorem finrank_gradedPiece_map (P : Ideal (MRing ι F₁)) (n : K → ℕ) :
    Module.finrank F₂ (gradedPiece (P.map (map (e : F₁ →+* F₂))) n) =
      Module.finrank F₁ (gradedPiece P n) := by
  let j₀ : gradedPiece P n →+ gradedPiece (P.map (map (e : F₁ →+* F₂))) n :=
    { toFun := fun x => ⟨quotEquiv e P x.1, quotEquiv_mem_gradedPiece e P n x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero (quotEquiv e P))
      map_add' := fun a b => Subtype.ext (map_add (quotEquiv e P) a.1 b.1) }
  have hinj : Function.Injective j₀ := fun a b h =>
    Subtype.ext ((quotEquiv e P).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective j₀ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
    have hg' : map (e.symm : F₂ →+* F₁) g ∈ weightedHomogeneousSubmodule F₁ (blockWeight ι) n := by
      rw [mem_weightedHomogeneousSubmodule] at hg ⊢
      have hgg : map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g) = g :=
        (mapEquiv (Σ k, ι k) e).apply_symm_apply g
      have h' : IsMultiHomog (map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g)) n := by
        rw [hgg]
        exact hg
      exact (isMultiHomog_map_iff e _ n).1 h'
    refine ⟨⟨Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g), Submodule.mem_map.2 ⟨_, hg', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change quotEquiv e P (Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g)) = Ideal.Quotient.mk _ g
    rw [quotEquiv_mk]
    congr 1
    exact (mapEquiv (Σ k, ι k) e).apply_symm_apply g
  let j := AddEquiv.ofBijective j₀ ⟨hinj, hsurj⟩
  have hrank := rank_eq_of_equiv_equiv (e : F₁ → F₂) j e.bijective (fun r m => by
    apply Subtype.ext
    exact quotEquiv_smul e P r m)
  unfold Module.finrank
  rw [hrank]

theorem hilbFn_map (P : Ideal (MRing ι F₁)) :
    hilbFn (P.map (map (e : F₁ →+* F₂))) = hilbFn P := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl

theorem intNum_map (P : Ideal (MRing ι F₁)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F₂ (P.map (map (e : F₁ →+* F₂))) bs = intNum F₁ P bs := by
  unfold intNum
  rw [hilbFn_map]

end Transport

end GenFibNef

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

