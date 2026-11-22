import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactor
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompat
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab

theorem exists_labelEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ f g : E →+* Ω, (∀ a : 𝓞 E, f (a : E) = g (a : E)) → f = g := by
    intro f g h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    exact h a
  rcases t with τ | τ
  · let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
    rw [H.bar_eq a]
  · let σ : E →+* Ω :=
      𝔐.cst.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (GlobalTheory.CompanionTheory.Ar.HT.cmConj E).toRingHom)
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
        𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
      rw [H.bar_eq a]
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1)
        (NumberField.IsCMField.complexConj E (NumberField.IsCMField.complexConj E (a : E)))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (a : E))
    rw [NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGivesChartPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem adjoin_int_le_chartQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {κ : Type} (x : κ → Ω) (c : κ) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ chartQ x c := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap r => simpa using intCast_mem (chartQ x c) r
  | add a b _ _ ha hb => exact (chartQ x c).add_mem ha hb
  | mul a b _ _ ha hb => exact (chartQ x c).mul_mem ha hb

theorem exists_prime_of_chart {Ω : Type} [Field Ω] [Algebra ℚ Ω] {X : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω} {c : κ} (hξ : IsCptGen ξ) {p : Cpt ξ}
    (hle : ∀ s ∈ chartQ x c, s ∈ regAt ξ p)
    (hdict : ∀ a ∈ regAt ξ p, ∃ s ∈ chartQ x c, unitAt ξ p s ∧ s * a ∈ chartQ x c) :
    ∃ I : Ideal (chartQ x c), I.IsPrime ∧ (∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (chartQ x c) I (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hξ p).1
  have hmem : ∀ s : chartQ x c, (s : Ω) ∈ regAt ξ p := fun s => hle _ s.2
  let f : chartQ x c →+* regAt ξ p :=
    ((chartQ x c).val : chartQ x c →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hu : ∀ s : chartQ x c,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  refine ⟨_, hI, hu, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hus, hsa⟩ := hdict a ha
    exact ⟨⟨s, hs⟩, (hu ⟨s, hs⟩).2 hus, hsa⟩
  · rintro ⟨s, hs, hsa⟩
    have hus := (hu s).1 hs
    have e : a = ((s : Ω) * a) * (s : Ω)⁻¹ := by
      field_simp [hus.1]
    rw [e]
    exact (regAt ξ p).mul_mem (hle _ hsa) hus.2.2

theorem exists_prime_chartQ : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → ∀ p : Cpt ξ, Char0 ξ p → InChart ξ x c p → ∃ I : Ideal (Mdl.chartQ x c), I.IsPrime ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  intro Ω _ _ X ξ κ x c hT p hp hc
  refine exists_prime_of_chart hT.gen (fun s hs => chartQ_le hp hc hs) fun a ha => ?_
  obtain ⟨s, hs, hus, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hT c p hc a).1 ha
  exact ⟨s, adjoin_int_le_chartQ x c hs, hus, adjoin_int_le_chartQ x c hsa⟩

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_charts_match_regular : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t → (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧ ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac | exact GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_generate_function_field : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω), CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac | exact GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_single_block_segre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω), CoordTie ℤ ξ x → CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k => ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | exact GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_component_in_some_chart : ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsModelVectorBundles
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.FlagBun in
theorem GlobalTheory.CompanionTheory.Ar.exists_flagBundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L hx hirr hL
  classical
  have hc : ∀ s, ∃ c : Fin (r s) → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = V s := by
    intro s
    obtain ⟨U, hU, b, hb, hfr⟩ := hL s ⟨genPt ξ, specializes_refl _⟩ trivial
    exact ⟨b, (hfr ⟨genPt ξ, specializes_refl _⟩ trivial hU).1, hb⟩
  choose c hc using hc
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x (L s) m φ :=
    fun s => GlobalTheory.T.exists_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) hx hirr (hL s)
  choose m n φ hφ using hg
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt ξ, specializes_refl _⟩
  have hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1 :=
    fun s => GlobalTheory.T.frame_via_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) (m s) (n s) (φ s) (c s) hx (hL s) (hφ s) (hc s).1 (hc s).2
  obtain ⟨J₀, hJ₀, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω E S r n κ x φ c c₀ hc₀.1 (GlobalTheory.T.function_field_ratio_generators X Ω ξ κ x c₀ hx hc₀.1) hB
  haveI : Finite (FlagIx κ n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx κ n r) (flagCoord κ x φ c) J₀ hJ₀ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular X Ω ξ ℤ κ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simpa using intCast_mem (regAt ξ' p') z) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord κ x φ c (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsurj := GlobalTheory.T.proper_dominating_surjective X Ω ξ κ x X' (GenField Ω r) ξ' s' f _ hx hirr hprop hdom
  have hsm := GlobalTheory.T.flag_frames_generic_model_right X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hfl := GlobalTheory.T.flag_frames_generic_model_left X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hgen := GlobalTheory.T.generic_flag_over_generic_field Ω E S r V c hc
  have hne : Nonempty (FlagIx κ n r) := ⟨J₀⟩
  have hpos : 0 < Nat.card (FlagIx κ n r) := Nat.card_pos
  let e : Fin (Nat.card (FlagIx κ n r) - 1 + 1) ≃ FlagIx κ n r :=
    (finCongr (Nat.sub_add_cancel hpos)).trans (Finite.equivFin (FlagIx κ n r)).symm
  exact ⟨X', GenField Ω r, inferInstance, inferInstance, ξ', f, _, flagCoord κ x φ c ∘ e, genB c,
    (by convert coordTie_comp_equiv hx' e using 1 <;> first | exact Subsingleton.elim _ _ | skip), hirr', hdom, hsm, hsurj, hgen, hfl⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisationStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_dominating_model : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation | exact GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation | (intros; apply GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizer
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Rescar

theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (n : ℕ) (hn : n ≠ 0) (hmem : (n : R) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : R) ∈ P := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    exact absurd (by simpa using hmem : (1 : R) ∈ P) (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h))
  | prime p hp => exact ⟨p, hp, hmem⟩
  | mul a b iha ihb =>
    have ha : a ≠ 0 := fun h => hn (by simp [h])
    have hb : b ≠ 0 := fun h => hn (by simp [h])
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact iha ha h
    · exact ihb hb h

theorem exists_prime_div_uniformiser (F' : Type) [Field F'] [NumberField F']
    (v : HeightOneSpectrum (𝓞 F')) (π : F') (hπ : v.valuation F' π = WithZero.exp (-1 : ℤ)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F') ∈ v.asIdeal := by
    simpa using Ideal.absNorm_mem v.asIdeal
  obtain ⟨ℓ, hℓ, hℓmem⟩ := exists_prime_natCast_mem v.asIdeal _ hne hmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hlt : v.valuation F' (ℓ : F') < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F') (ℓ : 𝓞 F')).2 hℓmem
    simpa using this
  have hle : v.valuation F' (ℓ : F') ≤ WithZero.exp (-1 : ℤ) := by
    rcases eq_or_ne (v.valuation F' (ℓ : F')) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, v.valuation F' (ℓ : F') = WithZero.exp a :=
        ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
      rw [ha] at hlt ⊢
      have h1 : a < 0 := by
        rw [← WithZero.exp_zero] at hlt
        exact WithZero.exp_lt_exp.1 hlt
      exact WithZero.exp_le_exp.2 (by omega)
  rw [map_div₀, hπ]
  exact div_le_one_of_le₀ hle zero_le'

end GlobalTheory.CompanionTheory.Ar.Rescar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_basis_of_factor : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsAbelianScheme A → Out.RelAmple A L → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) → ∃ (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), 0 < N ∧ (∀ i, Differentiable ℂ (Θ i)) ∧ (∀ i (l : u.Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) ∧ (∃ i, Θ i ≠ 0) ∧ ∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family | exact GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family | (intros; apply GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vertical_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω), GenUnit y a u → ∃ c : ℝ, VertBound y a u c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound | exact GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePull

theorem wedge_eq_span_pull {X₀ X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X ⟶ X₀} {i : Ω₀ →+* Ω}
    {V₀ V : Type} [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] {j : V₀ →+ V}
    (hD : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) (hE : IsExtOver i j) {L₀ : Lat ξ₀ V₀} {L : Lat ξ V} {n : ℕ}
    {a₀ : ⋀[Ω₀]^n V₀} {a : ⋀[Ω]^n V} (x : Cpt ξ) (h : genPt ξ₀ ⤳ f x.1) {u : Fin n → V₀} {α : Ω₀} (hα : α ≠ 0)
    (hF : L₀.IsFrameAt u ⟨f x.1, h⟩) (hL : L x = L₀.pull ξ f j x)
    (hW : L₀.wedge n ⟨f x.1, h⟩ = Submodule.span (regAt ξ₀ ⟨f x.1, h⟩) {α • a₀})
    (hP : CptIn.IsPullWedge i j a₀ a) :
    L.wedge n x = Submodule.span (regAt ξ x) {i α • a} := by
  obtain ⟨_, hreg, -⟩ := pull_reg_and_gen X₀ Ω₀ ξ₀ X Ω ξ f i hD x
  have hF' := FlagPull.pull_isFrameAt hD hE x h hF
  have hFr : L.IsFrameAt (fun k => j (u k)) x := ⟨hF'.1, hL.trans hF'.2⟩
  obtain ⟨hw, -⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L n _ x hFr
  obtain ⟨hw₀, hne⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L₀ n u _ hF
  obtain ⟨ε, hε, e⟩ := ZUnit.exists_of_span_eq hne (hw₀.symm.trans hW)
  have hεα : ε * α ≠ 0 := mul_ne_zero hε.1 hα
  have ha₀ : a₀ = (ε * α)⁻¹ • exteriorPower.ιMulti Ω₀ n u := by
    rw [e, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hεα, one_smul]
  have ha := hP u _ ha₀
  have hne' : i ε ≠ 0 := (map_ne_zero i).2 hε.1
  have hiα : i α ≠ 0 := (map_ne_zero i).2 hα
  have e2 : exteriorPower.ιMulti Ω n (fun k => j (u k)) = i ε • i α • a := by
    rw [ha, smul_smul, smul_smul, ← map_mul, ← map_mul, mul_inv_cancel₀ hεα, map_one, one_smul]
  rw [hw, e2]
  have hu : i ε ∈ regAt ξ x := hreg _ hε.2.1
  have hv : (i ε)⁻¹ ∈ regAt ξ x := by
    rw [← map_inv₀]
    exact hreg _ hε.2.2
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨i ε, hu⟩, rfl⟩
  · refine ⟨⟨(i ε)⁻¹, hv⟩, ?_⟩
    show (i ε)⁻¹ • i ε • i α • a = i α • a
    rw [inv_smul_smul₀ hne']

theorem isCoeffAt_pull : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  intro X₀ X Ω₀ Ω _ _ ξ₀ ξ f i V₀ V _ _ _ _ j A₀ B₀ A B p q a₀ b₀ a b x x₀ u₁ u₂ _ _ hD hE hx hF₁ hF₂ hA hB hC hPa hPb
  obtain ⟨α, β, hα, -, hAw, hBw, hαβ⟩ := hC
  rw [one_mul] at hαβ
  subst hαβ
  obtain ⟨y, hy⟩ := x₀
  obtain rfl : y = f x.1 := hx
  exact ⟨i α, i α, (map_ne_zero i).2 hα, (map_ne_zero i).2 hα,
    wedge_eq_span_pull hD hE x hy hα hF₁ hA hAw hPa, wedge_eq_span_pull hD hE x hy hα hF₂ hB hBw hPb, one_mul _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LinePull
end
end

