import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0023
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedGramDetPositive
section
open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

section Field

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

theorem eigSp_apply {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (hx : x ∈ eigSp ρ σ) (a : O) :
    ρ a x = σ a • x := by
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

theorem iSup_eigSp_stable (ρ : O →+* Module.End k V) (T : Set (O →+* k)) (a : O) {x : V}
    (hx : x ∈ ⨆ τ ∈ T, eigSp ρ τ) : ρ a x ∈ ⨆ τ ∈ T, eigSp ρ τ := by
  have hle : (⨆ τ ∈ T, eigSp ρ τ) ≤ (⨆ τ ∈ T, eigSp ρ τ).comap (ρ a) := by
    refine iSup₂_le fun τ hτ y hy => ?_
    rw [Submodule.mem_comap, eigSp_apply hy a]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ (Submodule.mem_iSup_of_mem hτ hy))
  exact hle hx

theorem eq_zero_of_mem_finset (ρ : O →+* Module.End k V) (σ : O →+* k)
    (t : Finset {τ : O →+* k // τ ≠ σ}) :
    ∀ x ∈ eigSp ρ σ, x ∈ (⨆ i ∈ t, eigSp ρ i.1) → x = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro x _ h
    simpa using h
  | insert τ t _ ih =>
    intro x hx hxs
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, hyz⟩ := hxs
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ τ.1 a := by
      by_contra h
      push_neg at h
      exact τ.2 (RingHom.ext fun a => (h a).symm)
    have hzs : ∀ b : O, ρ b z ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      intro b
      have hle : (⨆ i ∈ t, eigSp ρ i.1) ≤ (⨆ i ∈ t, eigSp ρ i.1).comap (ρ b) := by
        refine iSup₂_le fun i hi u hu => ?_
        rw [Submodule.mem_comap, eigSp_apply hu b]
        exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi hu))
      exact hle hz
    have hkey : (σ a - τ.1 a) • x = ρ a z - τ.1 a • z := by
      have e1 := eigSp_apply hx a
      have e2 := eigSp_apply hy a
      rw [← hyz, map_add, e2] at e1
      have e3 : ρ a z = σ a • (y + z) - τ.1 a • y := by rw [← e1]; abel
      rw [e3, ← hyz, sub_smul]
      simp only [smul_add]
      abel
    have hmem : (σ a - τ.1 a) • x ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      rw [hkey]
      exact Submodule.sub_mem _ (hzs a) (Submodule.smul_mem _ _ hz)
    have h0 := ih _ (Submodule.smul_mem _ _ hx) hmem
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 ha)

theorem eq_zero_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {x : V} (hx : x ∈ eigSp ρ σ)
    (hS : x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) : x = 0 := by
  have h : (⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) = ⨆ i : {τ : O →+* k // τ ≠ σ}, eigSp ρ i.1 := by
    rw [iSup_subtype']
    rfl
  rw [h, Submodule.mem_iSup_iff_exists_finset] at hS
  obtain ⟨t, ht⟩ := hS
  exact eq_zero_of_mem_finset ρ σ t x hx ht

theorem eigComp_spec {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (h0 : eigComp ρ σ x ≠ 0) :
    eigComp ρ σ x ∈ eigSp ρ σ ∧ x - eigComp ρ σ x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ := by
  by_cases h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ'
  · have e : eigComp ρ σ x = h.choose := by
      unfold eigComp
      rw [dif_pos h]
    rw [e]
    exact h.choose_spec
  · exact absurd (by unfold eigComp; rw [dif_neg h]) h0

end Field

section Main

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem linearIndependent_f (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ)
    (hO : IsOFamily A.ρ A.I v) (hA : A.IsAdapted s v q) (hq : ∀ i, (q i : V) ∈ A.eig s) :
    LinearIndependent (𝓞 L) fun c => A.f (q c) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  set S : Submodule L V := ⨆ τ ∈ {τ : 𝓞 E →+* L | τ ≠ A.σ s}, eigSp A.ρ τ with hSdef
  set p : Fin r → V := fun i => eigComp A.ρ (A.σ s) (v i) with hpdef
  have hfam_l : ∀ i : Fin r, A.fam s v q (Fin.castAdd k i) = p i := by
    intro i
    simp [LinPt.fam, hpdef]
  have hfam_r : ∀ c : Fin k, A.fam s v q (Fin.natAdd r c) = (q c : V) := by
    intro c
    simp [LinPt.fam]
  have hp : ∀ i, p i ∈ eigSp A.ρ (A.σ s) ∧ v i - p i ∈ S := by
    intro i
    refine eigComp_spec ?_
    have := hA.1.ne_zero (Fin.castAdd k i)
    rwa [hfam_l] at this
  set M : Submodule L V := Submodule.span L (Set.range p) ⊔ S with hMdef
  have hT : ∀ (a : 𝓞 E) (i : Fin r), A.ρ a (v i) ∈ M := by
    intro a i
    have e : A.ρ a (v i) = A.σ s a • p i + A.ρ a (v i - p i) := by
      rw [map_sub, eigSp_apply (hp i).1 a]
      abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · exact Submodule.mem_sup_right (iSup_eigSp_stable A.ρ _ a (hp i).2)
  have hoS : oSpan A.ρ v ≤ M.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨a, i, rfl⟩
    exact hT a i
  have hI : ∀ x ∈ A.I, x ∈ M := by
    intro x hx
    obtain ⟨n, hn, -, hnx⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hO.2.2 hx
    have h1 : n • x ∈ M := hoS hnx.1
    have hn0 : (n : L) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have h2 : x = (n : L)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  set w : A.Λ := ∑ c, g c • q c with hw
  have hwV : (w : V) = ∑ c, g c • (q c : V) := by
    simp [hw]
  have hfw : A.f w = 0 := by
    simpa [hw, map_sum] using hg
  have hwI : (w : V) ∈ Submodule.span (𝓞 L) (A.I : Set V) := (A.ker w).1 hfw
  have hwe : (w : V) ∈ eigSp A.ρ (A.σ s) := by
    have : (w : V) ∈ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L) := by
      rw [hwV]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c).2
    exact this
  have hwM : (w : V) ∈ M := by
    have hle : Submodule.span (𝓞 L) (A.I : Set V) ≤ M.restrictScalars (𝓞 L) :=
      Submodule.span_le.2 fun x hx => hI x hx
    exact hle hwI
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 hwM
  have hue : u ∈ eigSp A.ρ (A.σ s) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨i, rfl⟩
    exact (hp i).1
  have ht0 : t = 0 := by
    refine eq_zero_of_mem_iSup A.ρ (A.σ s) ?_ ht
    have : t = (w : V) - u := by rw [← hut]; abel
    rw [this]
    exact Submodule.sub_mem _ hwe hue
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hu
  have hzero : ∑ j, (Fin.append (fun i => - b i) (fun c => algebraMap (𝓞 L) L (g c)) j) • A.fam s v q j = 0 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hfam_l, hfam_r, neg_smul, algebraMap_smul,
      Finset.sum_neg_distrib]
    rw [hb, ← hwV, ← hut, ht0]
    simp
  have := Fintype.linearIndependent_iff.1 hA.1 _ hzero (Fin.natAdd r c)
  rw [Fin.append_right] at this
  exact RingOfIntegers.coe_injective (by simpa using this)

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open scoped ComplexOrder in

theorem gramDet_pos_of_adapted : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type)
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ)
    (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) →
    ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  intro E L Ψ _ _ _ _ V _ _ _ _ A s r k v q hO hA hq e
  have hli := Adapted.linearIndependent_f A s v q hO hA hq
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec A.Bq.metric e (A.f (q i))) =
      Matrix.of fun i j ↦ (A.Bq.metric.form e).inner
        ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q i)) ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q j)) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec A.Bq.metric e hli)).det_pos
  rw [hG] at hp
  exact (Complex.lt_def.1 hp).1

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicConstantsInRangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_constants_in_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range | exact GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyDedekindConstantsStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_dedekind_constants : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) →
    HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
      [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ →
    ∀ (V : Type) [AddCommGroup V] [Module Ω V] (r : ℕ) (b : Fin r → V), LinearIndependent Ω b →
    ∀ (L L' : Lat ξ V) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' b Q →
      (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) →
      ∃ (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
        (∀ c, segreVec y c ≠ 0 → B.lat c = coordLat O y L b c ∧ B'.lat c = coordLat O y L' b c) ∧
        IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord | exact GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicative
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusPoints

theorem charVal_eq_diag {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A] {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) (χ : X) : charVal t χ = GlobalTheory.Diag.charVal t χ := by
  rw [GlobalTheory.Diag.charVal_eq_torusFst]
  rfl

theorem main : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  intro S X _ A _ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' h
    refine GlobalTheory.Diag.charVal_ext fun χ => ?_
    rw [← charVal_eq_diag, ← charVal_eq_diag]
    exact h χ
  · intro t t' χ
    rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_mul]
  · intro χ
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_one]
  · intro t
    refine ⟨?_, fun χ χ' => ?_⟩
    · rw [charVal_eq_diag, GlobalTheory.Diag.charVal_zero]
    · rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_add]
  · intro w
    refine ⟨GlobalTheory.Diag.ofVal a w, fun χ => ?_⟩
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_ofVal]
  · intro A' _ g t t' ht χ
    rw [charVal_eq_diag, charVal_eq_diag]
    exact (GlobalTheory.Diag.left_eq_iff g rfl t' t).1 ht χ

end GlobalTheory.CompanionTheory.Ar.TorusPoints
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

theorem closedPoint_germ_const {X : Scheme.{0}} {F : Type} [Field F] {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = φ o := by
  letI : Algebra O F := φ.toAlgebra
  have h := GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const z s hz ⟨genPt z, specializes_rfl⟩ o
  have e : genMap z ⟨genPt z, specializes_rfl⟩ = (Scheme.stalkClosedPointTo z).hom := by
    ext t
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    exact congrArg (fun q : X.presheaf.stalk (genPt z) ⟶ CommRingCat.of F => q.hom t)
      (Category.id_comp (Scheme.stalkClosedPointTo z))
  rw [e] at h
  exact h

theorem val_const {X : Scheme.{0}} {Ω : Type} [Field Ω] {F : Type} [Field F] {O : Type} [CommRing O]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (all : ∀ q : X, genPt ξ ⤳ q)
    (s : X ⟶ Spec (CommRingCat.of O)) (ψ : O →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom ψ))
    (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) : ValAt ξ z (ψ o) (φ o) := by
  letI : Algebra O Ω := ψ.toAlgebra
  exact ⟨all _, _, GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, all _⟩ o, closedPoint_germ_const s z φ hz o⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB OverVal

theorem isOver_base {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {z : Sp ℂ ⟶ 𝔐.X} {κ : c.F →+* ℂ}
    {p : Sp ℂ ⟶ Xo.X} (h : IsOver 𝔐 z κ p) :
    z ≫ 𝔐.f ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  obtain ⟨x, hx, -, hk⟩ := h
  have h1 : z ≫ 𝔐.f ≫ Y.s = x ≫ Y.j ≫ Y.s := by
    rw [← Category.assoc, ← hx, Category.assoc]
  rw [h1, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hk]
  exact (Spec.map_comp _ _).symm

theorem val_cst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z κ p h x
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hc : ∀ o : 𝓞 c.F, ValAt 𝔐.ξ z (𝔐.cst (algebraMap (𝓞 c.F) c.F o)) (κ (algebraMap (𝓞 c.F) c.F o)) := fun o =>
    val_const 𝔐.ξ 𝔐.all (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over z
      (κ.comp (algebraMap (𝓞 c.F) c.F)) (isOver_base h) o
  obtain ⟨a, n, hn, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
  have hn0 : algebraMap (𝓞 c.F) c.F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 c.F) c.F)).2 (nonZeroDivisors.ne_zero hn)
  have hk0 : κ (algebraMap (𝓞 c.F) c.F n) ≠ 0 := (map_ne_zero κ).2 hn0
  rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
  exact val_mul (hc a) (by simpa only [map_inv₀] using val_inv₀ hk0 (hc n))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_valuation_bound_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L)
    (v : FinitePlace L) (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L] (zA : Sp A ⟶ X),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ r : A, v (algebraMap A L r) ≤ 1) → (∀ r : A, v (algebraMap A L r) = 1 → IsUnit r) →
    CoordsAt ξ y (spMap (algebraMap A L) ≫ zA) w →
    ∃ (c : (k : K) → J k) (h : genPt ξ ⤳ centre zA), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
      (∀ k i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c k⟩)) ∧
      InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zA, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite | exact GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_at_complex_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding | exact GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem closure_finiteType_over_int : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) :=
  @PositivityTheory.Xgn.coordinate_map_finite_type

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberPointsGlueStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_number_points_glue : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  (∀ a b : Sp R ⟶ X, (∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a = spMap (algebraMap R (Localization.Away (f i))) ≫ b) → a = b) ∧
  (∀ a b : Sp (DualNumber R) ⟶ X,
    (∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) → a = b) ∧
  ∀ w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X,
    (∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j)) (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j) →
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ v = w i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue | exact GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormalCoverGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem normalisation_finite_cover :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z :=
  @PositivityTheory.Xgn.stratum_finite_normal_cover

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveLiftsPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem exists_lift_algClosure : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ :=
  PositivityTheory.Xgn.finite_surjective_point_lift

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveOpenImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Strat

theorem preimage_le_of_finite_surjective : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V :=
  PositivityTheory.Xgn.finite_surjective_image_open

end GlobalTheory.CompanionTheory.Ar.Strat
end

