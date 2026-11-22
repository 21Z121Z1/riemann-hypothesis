import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PotentialBoundedPshBoth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeRangeOfStalkStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_range_of_stalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range | exact GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_points_existsUnique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ w : (Σ k, J k) → R, (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) → ∃! z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w) ∧ (∀ z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z → ∃ w, CoordsAt ξ y z w) ∧ ∀ (z : Spec (CommRingCat.of R) ⟶ X) w, genPt ξ ⤳ centre z → CoordsAt ξ y z w → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) ∧ ∀ w', CoordsAt ξ y z w' ↔ ∃ a : K → Rˣ, w' = fun p => (a p.1 : R) * w p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.tie_points | exact GlobalTheory.CompanionTheory.Ar.tie_points | (intros; apply GlobalTheory.CompanionTheory.Ar.tie_points <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqual
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem inv_mem_locSub_prod {K : Type} [Field K] {Q : Type} [Fintype Q] (D : Subring K) (s : Q → K)
    (h0 : ∀ q, s q ≠ 0) (hD : ∀ q, s q ∈ D) (q : Q) : (s q)⁻¹ ∈ locSub D (∏ q, s q) := by
  classical
  have hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q' :=
    Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)
  have hne : (∏ q', s q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'
  have e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q' := by
    rw [← hprod] at hne ⊢
    have h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0 := right_ne_zero_of_mul hne
    field_simp [h0 q, h1]
  rw [e]
  exact (locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _)
    (le_locSub D _ (D.prod_mem fun q' _ => hD q'))

theorem locSub_eq_of_inverse_family : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K),
    (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) →
    A ≤ Subring.closure ((B : Set K) ∪ Set.range t) →
    B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) →
    locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  intro K _ Q _ A B t h0 hA hB hAB hBA
  have hT : (∏ q, t q) ∈ A := A.prod_mem fun q _ => hA q
  have hTi : (∏ q, t q)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    exact B.prod_mem fun q _ => hB q
  have hBle : B ≤ locSub A (∏ q, t q) := by
    refine hBA.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub A _ hx
    · exact inv_mem_locSub_prod A t h0 hA q
  have hAle : A ≤ locSub B (∏ q, t q)⁻¹ := by
    refine hAB.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub B _ hx
    · have h := inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q
      rw [Finset.prod_inv_distrib] at h
      simpa using h
  refine le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)
  · rintro x (hx | hx)
    · exact hAle hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_locSub B _ hTi
  · rintro x (hx | hx)
    · exact hBle hx
    · rw [Set.mem_singleton_iff.1 hx, inv_inv]
      exact le_locSub A _ hT

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmooth
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem smooth_of_away_mvPolynomial {R L ι : Type} [CommRing R] [CommRing L] [Finite ι]
    (g : R →+* L) (ψ : MvPolynomial ι R →+* L) (hg : ψ.comp MvPolynomial.C = g) (f : MvPolynomial ι R)
    (hl : @IsLocalization.Away _ _ f L _ ψ.toAlgebra) : g.Smooth := by
  letI := ψ.toAlgebra
  haveI := hl
  have h1 : ψ.Smooth := (Algebra.Smooth.of_isLocalization_Away f : Algebra.Smooth (MvPolynomial ι R) L)
  have h2 : (algebraMap R (MvPolynomial ι R)).Smooth :=
    RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  rw [MvPolynomial.algebraMap_eq] at h2
  rw [← hg]
  exact RingHom.Smooth.comp h2 h1

def evalSub {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω) (v : ι → K) :
    MvPolynomial ι R →+* K :=
  MvPolynomial.eval₂Hom ((algebraMap Ω K).comp R.subtype) v

theorem evalSub_injective {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) (hv : AlgebraicIndependent Ω v) : Function.Injective (evalSub R v) := by
  have e : evalSub R v =
      (MvPolynomial.aeval v : MvPolynomial ι Ω →ₐ[Ω] K).toRingHom.comp (MvPolynomial.map R.subtype) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evalSub]
    · intro i
      simp [evalSub]
  rw [e]
  exact fun p q hpq => MvPolynomial.map_injective _ R.subtype_injective
    (algebraicIndependent_iff_injective_aeval.1 hv hpq)

theorem evalSub_range {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) : (evalSub R v).range =
      Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C a =>
      refine Subring.subset_closure (Or.inl ⟨a, a.2, ?_⟩)
      simp [evalSub]
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subring.subset_closure (Or.inr ⟨i, ?_⟩))
      simp [evalSub]
  · refine Subring.closure_le.2 ?_
    rintro x (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [evalSub]⟩
    · exact ⟨MvPolynomial.X i, by simp [evalSub]⟩

theorem smooth_locSub_closure : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  intro Ω K _ _ _ ι _ R v hv ℓ hℓ h0 h
  have hr := evalSub_range R v
  generalize Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) = B at *
  subst hr
  have hinj := evalSub_injective R v hv
  have hmem : ∀ a, evalSub R v a ∈ locSub (evalSub R v).range ℓ :=
    fun a => le_locSub _ _ ⟨a, rfl⟩
  obtain ⟨f, hf⟩ := hℓ
  refine smooth_of_away_mvPolynomial _ ((evalSub R v).codRestrict _ hmem) ?_ f ?_
  · ext a
    change evalSub R v (MvPolynomial.C a) = algebraMap Ω K a
    simp [evalSub]
  · letI := ((evalSub R v).codRestrict _ hmem).toAlgebra
    have hval : ∀ a : MvPolynomial ι R,
        ((algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) a : locSub (evalSub R v).range ℓ) : K)
          = evalSub R v a := fun a => rfl
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨_, n, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) f) := by
        refine IsUnit.of_mul_eq_one ⟨ℓ⁻¹, inv_mem_locSub _ _⟩ (Subtype.ext ?_)
        simp [hval, hf, h0]
      simpa using hu.pow n
    · rintro ⟨z, hz⟩
      obtain ⟨k, hk⟩ := (mem_locSub_iff (RingHom.mem_range.2 ⟨f, hf⟩) h0 z).1 hz
      obtain ⟨a, ha⟩ := RingHom.mem_range.1 hk
      refine ⟨⟨a, ⟨f ^ k, k, rfl⟩⟩, Subtype.ext ?_⟩
      simp [hval, hf, ha, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [hinj (congrArg Subtype.val hxy)]⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinors
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_lu_of_leading_minors {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (h : ∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧
      (∀ l, V l l = 1) ∧ Y * C = V := by
  classical
  let B : ∀ k : Fin r, Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) F := fun k =>
    Y.submatrix (Fin.castLE k.2) (Fin.castLE k.2)
  have hB : ∀ k, IsUnit (B k).det := fun k => isUnit_iff_ne_zero.2 (h _ k.2)
  let a : ∀ k : Fin r, Fin ((k : ℕ) + 1) → F := fun k =>
    (B k)⁻¹.mulVec (Pi.single (Fin.last _) 1)
  have ha : ∀ k, (B k).mulVec (a k) = Pi.single (Fin.last _) 1 := fun k => by
    simp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB k), Matrix.one_mulVec]
  let C : Matrix (Fin r) (Fin r) F := fun l k =>
    if hlk : (l : ℕ) < (k : ℕ) + 1 then a k ⟨l, hlk⟩ else 0
  have hV : ∀ (k : Fin r) (l : Fin ((k : ℕ) + 1)),
      (Y * C) (Fin.castLE k.2 l) k = (Pi.single (Fin.last (k : ℕ)) (1 : F) :
        Fin ((k : ℕ) + 1) → F) l := by
    intro k l
    rw [← ha k]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    symm
    refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun j _ hj => ?_) (fun b _ => ?_)
    · have hjk : ¬ (j : ℕ) < (k : ℕ) + 1 := fun hlt =>
        hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
      simp only [C, dif_neg hjk, mul_zero]
    · have hb : ((Fin.castLE k.2 b : Fin r) : ℕ) < (k : ℕ) + 1 := b.2
      simp only [C, dif_pos hb]
      rfl
  refine ⟨C, Y * C, fun l k hkl => ?_, fun l k hlk => ?_, fun l => ?_, rfl⟩
  · have hn : ¬ (l : ℕ) < (k : ℕ) + 1 := by
      have : (k : ℕ) < l := hkl
      omega
    simp only [C, dif_neg hn]
  · have hlt : (l : ℕ) < (k : ℕ) + 1 := by
      have : (l : ℕ) < k := hlk
      omega
    have h1 := hV k ⟨l, hlt⟩
    have e : Fin.castLE k.2 (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) = l := by ext; simp
    have hne : (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) ≠ Fin.last (k : ℕ) := by
      intro hh
      have h2 : (l : ℕ) = k := by simpa using Fin.ext_iff.1 hh
      have : (l : ℕ) < k := hlk
      omega
    rw [e, Pi.single_eq_of_ne hne] at h1
    exact h1
  · have h1 := hV l (Fin.last (l : ℕ))
    have e : Fin.castLE l.2 (Fin.last (l : ℕ)) = l := by ext; simp
    rw [e, Pi.single_eq_same] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_btOrder_iff_mem_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U :=
  PositivityTheory.HtPt.Twhopf.mem_order

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MonoLinesLineSmooth
section
noncomputable section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem line_smooth_at (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem line_a_eq (M : RootModel Ψ N) (t s : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line s j).a := by
  cases j with
  | none => rfl
  | some r => exact (M.x_deg t r).trans (M.x_deg s r).symm

theorem monoLines_line_smooth (M : RootModel Ψ N) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsSmoothHerm (monoLines (M.line t) m d k) := by
  unfold monoLines
  split_ifs with h
  · exact line_smooth_at M t _
  · exact contDiffOn_const

theorem monoLines_line_a (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    (monoLines (M.line t) m d k).a = (monoLines (M.line s) m d k).a := by
  unfold monoLines
  split_ifs with h
  · exact line_a_eq M t s _
  · rfl

theorem ptsIntegral_line_eq (hD : DegreeStatement) (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    ptsIntegral M.P (pot (monoLines (M.line t) m (dimFl Ψ N))) (fun _ => 1) =
      ptsIntegral M.P (pot (monoLines (M.line s) m (dimFl Ψ N))) (fun _ => 1) := by
  rw [hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M t m _) Nat.prime_two,
    hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M s m _) Nat.prime_two]
  simp only [monoLines_line_a M t s m]

theorem geoMono_eq (hD : DegreeStatement) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ)
    (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N) :
    ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (fun _ => 1) / (M.δ : ℝ) =
      M.geoMono (m.mapDomain some) := by
  have hdeg : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hnone : (m.mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  rw [ptsIntegral_line_eq hD M t 1]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem stalk_isDiscreteValuationRing_of_dim_one : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) :=
  @PositivityTheory.UnitarySelfGeneration.normal_scheme_height_one_stalk_dvr

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtends
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem det_mem_subring {F : Type} [CommRing F] (D : Subring F) {k : ℕ} (A : Matrix (Fin k) (Fin k) F)
    (hA : ∀ a b, A a b ∈ D) : A.det ∈ D := by
  rw [Matrix.det_apply']
  exact D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem mul_adjugate_apply_eq_kMinor {F : Type} [Field F] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (m : ℕ)
    (hm : m ≤ r) (J : Fin m → Fin n) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      kMinor Y m hm (Function.update J j i) := by
  classical
  have h1 : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      Matrix.cramer (Y.submatrix J (Fin.castLE hm)).transpose (Y.submatrix id (Fin.castLE hm) i) j := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h1, Matrix.cramer_transpose_apply]
  unfold kMinor
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab
    simp
  · simp [Matrix.updateRow_ne hab, Function.update_of_ne hab]

theorem normAt_mul_inv_mem {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (m : ℕ) (hm : m ≤ r) (J : Fin m → Fin n) (hJ : NormAt O Y m hm J) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j ∈ O := by
  classical
  have e : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j =
      kMinor Y m hm (Function.update J j i) / kMinor Y m hm J := by
    rw [Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, mul_adjugate_apply_eq_kMinor,
      Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]
    rfl
  rw [e]
  exact hJ.2 _

theorem normAt_exchange {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n)
    (h' : NormAt O Y (k + 1) hk I') (h : NormAt O Y k (Nat.le_of_succ_le hk) I) :
    ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  classical
  have hk0 : k ≤ r := Nat.le_of_succ_le hk
  have hM' : IsUnit (Y.submatrix I' (Fin.castLE hk)).det := isUnit_iff_ne_zero.2 h'.1
  have hM : IsUnit (Y.submatrix I (Fin.castLE hk0)).det := isUnit_iff_ne_zero.2 h.1
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = Y.submatrix id (Fin.castLE hk) * (Y.submatrix I' (Fin.castLE hk))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Z', hZ'def⟩ : ∃ Z', Z' = Y.submatrix id (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ :=
    ⟨_, rfl⟩
  have hZ : ∀ a b, Z a b ∈ O := fun a b => by
    rw [hZdef]; exact normAt_mul_inv_mem O Y _ hk I' h' a b
  have hZ' : ∀ a b, Z' a b ∈ O := fun a b => by
    rw [hZ'def]; exact normAt_mul_inv_mem O Y _ hk0 I h a b
  have e1 : Y.submatrix id (Fin.castLE hk) = Z * Y.submatrix I' (Fin.castLE hk) := by
    rw [hZdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM', Matrix.mul_one]
  have hY0 : Y.submatrix id (Fin.castLE hk0) = Z * (Y.submatrix I' (Fin.castLE hk0)) := by
    ext a b
    have := congrFun (congrFun e1 a) (Fin.castSucc b)
    simpa [Matrix.mul_apply] using this
  have hD : ∀ {m : ℕ} (J : Fin m → Fin n), Z'.submatrix J id =
      Y.submatrix J (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ := by
    intro m J
    rw [hZ'def]
    ext a b
    simp [Matrix.mul_apply]
  have hZZ : Z' = Z * Z'.submatrix I' id := by
    rw [hD, ← Matrix.mul_assoc, ← hY0, hZ'def]
  have hI : Z'.submatrix I id = 1 := by
    rw [hD, Matrix.mul_nonsing_inv _ hM]
  have hone : Z.submatrix I id * Z'.submatrix I' id = 1 := by
    rw [← hI]
    conv_rhs => rw [hZZ]
    ext a b
    simp [Matrix.mul_apply]
  have hsum := det_mul_expand (Z.submatrix I id) (Z'.submatrix I' id)
  rw [hone, Matrix.det_one] at hsum
  obtain ⟨f, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun f _ => O.mul_mem (O.prod_mem fun a _ => hZ _ _) (det_mem_subring O _ fun a b => hZ' _ _)) hsum.symm
  have hc : (∏ a, (Z.submatrix I id) a (f a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : ((Z'.submatrix I' id).submatrix f id).det ≠ 0 := right_ne_zero_of_mul hne
  have hdet : ((Z'.submatrix I' id).submatrix f id).det =
      kMinor Y k hk0 (I' ∘ f) / kMinor Y k hk0 I := by
    have e2 : (Z'.submatrix I' id).submatrix f id = Z'.submatrix (I' ∘ f) id := by
      ext a b; simp
    rw [e2, hD, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_eq_mul_inv]
    rfl
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne'
    exact hd (Matrix.det_zero_of_row_eq hne' (by ext c; simp [hab]))
  refine ⟨f, hinj, ?_, fun I'' => ?_⟩
  · intro h0
    apply hd
    rw [hdet, h0, zero_div]
  · have hP := h.1
    have hQ : kMinor Y k hk0 (I' ∘ f) ≠ 0 := by
      intro h0
      apply hd
      rw [hdet, h0, zero_div]
    have e : kMinor Y k hk0 I'' / kMinor Y k hk0 (I' ∘ f) =
        (kMinor Y k hk0 I'' / kMinor Y k hk0 I) * ((∏ a, (Z.submatrix I id) a (f a)) *
          ((∏ a, (Z.submatrix I id) a (f a)) * ((Z'.submatrix I' id).submatrix f id).det)⁻¹) := by
      rw [hdet]
      field_simp
    rw [e]
    exact O.mul_mem (h.2 I'') (O.mul_mem (O.prod_mem fun a _ => hZ _ _) hinv)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompareStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_valuation_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order | exact GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElementStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_localization_at_element : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (R : Subring Ω) (a : Ω), IsCptGen ξ → IsPiece ξ U R → a ∈ R → a ≠ 0 → ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PotentialBoundedPshBothStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_bounded_psh_both : ∀ (e : ℕ) (σ : Type) (S : PB.AnSys e σ) (a : σ), (∀ t, ReciprocityTheory.AnForm.M.IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ ReciprocityTheory.AnForm.M.IsPsh S.A (S.potT a t)) → ∃ C : ℝ, ∀ t, 0 < t → t ≤ S.t₀ → ∀ x, |S.phT a t x| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | exact GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded <;> assumption)
end

