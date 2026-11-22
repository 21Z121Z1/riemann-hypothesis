import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0068
import Formalism.HermitianLattices.FinalMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMassesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, (∀ Q : ℕ → Prop, (S.sumData fun d => S.nT d C fun Λ => Q (S.be d Λ)) ≤ ∑' Mh : {Mh : Submodule L.O S.V // S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) ∧ Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup)}, S.massSig Mh) ∧ (S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ) = S.massSig (S.Mof p.1 p.2) := by
  first | exact @GlobalTheory.HL.ClassMass.class_mass | exact GlobalTheory.HL.ClassMass.class_mass | (intros; apply GlobalTheory.HL.ClassMass.class_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameClasses_total_weight_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∃ d Λ, S.IsTerm d Λ) → (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  first | exact @GlobalTheory.HL.TotalWeight.sumCls_one_le | exact GlobalTheory.HL.TotalWeight.sumCls_one_le | (intros; apply GlobalTheory.HL.TotalWeight.sumCls_one_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbitsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) ∧ LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧ (∑' t : R.RT d, ENNReal.ofReal (LocNG.mu P t.1)) = S.mass (c.dat d) (fun _ => True) := by
  first | exact @GlobalTheory.HL.CoordAmp.amp_mass_eq | exact GlobalTheory.HL.CoordAmp.amp_mass_eq | (intros; apply GlobalTheory.HL.CoordAmp.amp_mass_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbitsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePair_tsum_reps_eq_const_mul_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  first | exact @GlobalTheory.HL.CoordSum.tsum_reps_eq | exact GlobalTheory.HL.CoordSum.tsum_reps_eq | (intros; apply GlobalTheory.HL.CoordSum.tsum_reps_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEq
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.GenusOrb

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] in

theorem _root_.GlobalTheory.Mass.GenusOrb.trace_pos_of_PD (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hp : _root_.GlobalTheory.Mass.PD h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have hp' : ∀ (τ : K →+* ℂ) (x : V), x ≠ 0 → 0 < (τ ((h x) x)).re := hp
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := h x x)
  have hre : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re =
      (Algebra.trace ℚ K (h x x) : ℝ) := by simp
  have hpos : (0 : ℝ) < (Algebra.trace ℚ K (h x x) : ℝ) := by
    rw [← hre, hsum, Complex.re_sum]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨φ.toRatAlgHom⟩
    exact Finset.sum_pos (fun σ _ => hp' σ.toRingHom x hx) Finset.univ_nonempty
  exact_mod_cast hpos

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def autEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    Formalism.ThetaLiftIndependence.autL h M ≃ MulAction.stabilizer (isom h) M where
  toFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

open NumberField Matrix in
open scoped ENNReal Classical in

theorem _root_.GlobalTheory.Mass.GenusOrb.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    0 < _root_.Formalism.HermitianLatticesTheory.mass h L ∧ _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M)) ∧
    ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s →
      (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by
  intro K V _ _ _ _ _ _ _ _ h _ hsymm hp L hL
  have htr : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) :=
    _root_.GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hp
  obtain ⟨hmass_ex, hmass_eq, hmass_pos⟩ := _root_.Formalism.HermitianLatticesTheory.final_massBasic K V h hsymm htr L hL
  have hgen : ∀ g ∈ _root_.Formalism.HermitianLatticesTheory.isom h, ∀ M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L, _root_.Formalism.HermitianLatticesTheory.gmap g M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L := by
    intro g hg M hM
    obtain ⟨hML, hLM⟩ := hM
    obtain ⟨heq, hinv, -⟩ := _root_.Formalism.HermitianLatticesTheory.final_genusBasic (𝓞 K) K V h hsymm _root_.Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
    exact show Submodule.IsLattice K (_root_.Formalism.HermitianLatticesTheory.gmap g M) ∧ _root_.Formalism.HermitianLatticesTheory.SameGenus h L (_root_.Formalism.HermitianLatticesTheory.gmap g M) from
      ⟨(_root_.Formalism.HermitianLatticesTheory.final_isomAct (𝓞 K) K V h g hg M).2.2.2.2.mpr hML, heq.trans hLM (hinv M g hg)⟩
  have hstab : _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := fun g M hM => hgen g.1 g.2 M hM
  have hfin : ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M) := by
    intro M hM
    have hS := _root_.Formalism.HermitianLatticesTheory.final_autFinite K V h hsymm htr M hM
    haveI := hS.to_subtype
    refine Finite.of_injective (fun g : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M =>
      (⟨g.1.1, g.1.2, g.2⟩ : {g | g ∈ _root_.Formalism.HermitianLatticesTheory.isom h ∧ _root_.Formalism.HermitianLatticesTheory.gmap g M = M})) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hsum : ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞),
      _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by
    intro s N hs hN
    obtain ⟨hsub, huniq⟩ := hs
    rw [_root_.GlobalTheory.Mass.orbSum_eq_sum_reps (_root_.Formalism.HermitianLatticesTheory.isom h) _ _ N hstab hN s hsub ?_]
    · refine Finset.sum_congr rfl fun M hM => ?_
      congr 1
      obtain ⟨hMlat, -⟩ := hsub M hM
      haveI := hfin M hMlat
      haveI : Finite (_root_.Formalism.ThetaLiftIndependence.autL h M) :=
        Finite.of_equiv _ (_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M).symm
      haveI : Nonempty (_root_.Formalism.ThetaLiftIndependence.autL h M) := ⟨(_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M).symm 1⟩
      have hpos : (0 : ℝ) < (Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ) := by exact_mod_cast Nat.card_pos
      rw [← ENat.card_congr (_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M), ENat.card_eq_coe_natCard,
        ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
      norm_cast
    · intro M hM
      obtain ⟨y, ⟨hy, g, hg, hgy⟩, huy⟩ := huniq M hM
      exact ⟨y, ⟨hy, ⟨g, hg⟩, hgy⟩, fun z ⟨hz, g', hg'⟩ => huy z ⟨hz, g'.1, g'.2, hg'⟩⟩
  obtain ⟨s, hs⟩ := hmass_ex
  have h1 : ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := by
    rw [hmass_eq s hs, ENNReal.ofReal_sum_of_nonneg (fun M _ => by positivity)]
    have := hsum s (fun _ => 1) hs (fun _ _ => rfl)
    simp only [mul_one] at this
    rw [this]
    rfl
  exact ⟨h1, hmass_pos, hstab, hfin, hsum⟩

end GlobalTheory.Mass.GenusOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevelsStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMove_preserves_frameLattice_levels : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.IsTerm d Λ₁ ∧ ∀ y ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)), (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧ S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y := by
  first | exact @GlobalTheory.HL.MoveSame.move_same | exact GlobalTheory.HL.MoveSame.move_same | (intros; apply GlobalTheory.HL.MoveSame.move_same <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimatesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMoves_total_measure_estimates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → Nice (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) ∧ Nice (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) ∧ Nice (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1) ∧ |S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ))).re - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * ‖cint (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.MoveTotal.total_moves | exact GlobalTheory.HL.MoveTotal.total_moves | (intros; apply GlobalTheory.HL.MoveTotal.total_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTermCount_frameClass_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (j : ℕ), (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  first | exact @GlobalTheory.HL.TermCount.nT_cardI_le | exact GlobalTheory.HL.TermCount.nT_cardI_le | (intros; apply GlobalTheory.HL.TermCount.nT_cardI_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_polar_form : PI.RhsWLim.W.RI.HypQ := by
  first | exact @GlobalTheory.HyperboloidPolar.hypQ | exact GlobalTheory.HyperboloidPolar.hypQ | (intros; apply GlobalTheory.HyperboloidPolar.hypQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolEqInfMulSupAndMono
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IndexProd

theorem relIndex_eq_of_forall_mul {G : Type*} [Group G] {D N E : Subgroup G} (hNE : N ≤ E)
    (h : ∀ e ∈ E, ∃ n ∈ N, ∃ d ∈ D, n * d = e) : D.relIndex E = D.relIndex N := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H e =>
    obtain ⟨n, hn, d, hd, hnd⟩ := h e e.2
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hnd] using hd

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A M : Subgroup G}
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) {x : G} (hx : x ∈ A ⊔ M) :
    ∃ a ∈ A, ∃ m ∈ M, a * m = x := by
  have hle : A ≤ Subgroup.normalizer M := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨h s hs t, fun ht => ?_⟩
    have := h s⁻¹ (A.inv_mem hs) _ ht
    simpa [mul_assoc] using this
  have hx' : x ∈ ((A ⊔ M : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A M hle] at hx'
  obtain ⟨a, ha, m, hm, e⟩ := hx'
  exact ⟨a, ha, m, hm, e⟩

theorem relIndex_eq_inf_mul_sup {G : Type*} [Group G] {D A M : Subgroup G} (hDA : D ≤ A)
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) :
    D.relIndex A = (D ⊓ M).relIndex (A ⊓ M) * (D ⊔ M).relIndex (A ⊔ M) := by
  have h1 : (D ⊔ M).relIndex (A ⊔ M) = (D ⊔ M).relIndex A :=
    relIndex_eq_of_forall_mul le_sup_left fun e he => by
      obtain ⟨a, ha, m, hm, e⟩ := exists_mul_of_mem_sup h he
      exact ⟨a, ha, m, (le_sup_right : M ≤ D ⊔ M) hm, e⟩
  have h2 : D.relIndex ((D ⊔ M) ⊓ A) = D.relIndex (A ⊓ M) :=
    relIndex_eq_of_forall_mul (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
      fun e he => by
        obtain ⟨d, hd, m, hm, e'⟩ := exists_mul_of_mem_sup (fun s hs => h s (hDA hs)) he.1
        refine ⟨d * m * d⁻¹, ⟨?_, h d (hDA hd) m hm⟩, d, hd, by rw [← e']; simp⟩
        rw [e']
        exact A.mul_mem he.2 (A.inv_mem (hDA hd))
  have h3 : (D ⊓ M).relIndex (A ⊓ M) = D.relIndex (A ⊓ M) := by
    rw [← Subgroup.inf_relIndex_right D, ← Subgroup.inf_relIndex_right (D ⊓ M)]
    congr 1
    rw [inf_comm A M, ← inf_assoc, ← inf_assoc, inf_assoc D M M, inf_idem]
  rw [h1, h3, ← h2, Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.2 le_sup_left]

theorem invVol_eq_inf_mul_sup_and_mono : ∀ (G : Type) [Group G] (R M A B : Subgroup G), M ≤ R → A ≤ R → B ≤ R → (∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ M) (B ⊓ M) * GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) ∧ ∀ B' ≤ B, B'.relIndex A ≠ 0 → A.relIndex B' ≠ 0 → GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' ∧ GlobalTheory.HL.invVol A B ≤ (B'.relIndex A : ℝ) := by
  intro G _ R M A B _ hA hB hn hAB hBA
  constructor
  · have eA := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_left
      (fun s hs => hn s (hA hs))
    have eB := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_right
      (fun s hs => hn s (hB hs))
    have dA : (A ⊓ B).relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dA' := dA
    rw [eA, mul_ne_zero_iff] at dA'
    rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA,
      GlobalTheory.HL.invVol_eq_div_of_le (inf_le_inf_right M inf_le_left)
        (inf_le_inf_right M inf_le_right) dA'.1,
      GlobalTheory.HL.invVol_eq_div_of_le (sup_le_sup_right inf_le_left M)
        (sup_le_sup_right inf_le_right M) dA'.2, eA, eB]
    push_cast
    rw [div_mul_div_comm]
  · intro B' hB' h1 h2
    have dA : (A ⊓ B').relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dB : (A ⊓ B').relIndex B ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero hAB (Subgroup.relIndex_ne_zero_trans h1 hAB)
    have dB' : (A ⊓ B').relIndex B' ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
    have hle : GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' := by
      rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left (inf_le_right.trans hB') dA,
        GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.pos_of_ne_zero dB') ?_
      exact_mod_cast Subgroup.relIndex_le_of_le_right hB' dB
    refine ⟨hle, hle.trans ?_⟩
    rw [GlobalTheory.HL.invVol]
    exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero h2)

end GlobalTheory.IndexProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
section
open NumberField

namespace GlobalTheory.EtaValueBound

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

theorem summable_zeta (M : ℕ) (hM : 2 ≤ M) : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
  simpa using this

theorem zeta_le_two (M : ℕ) (hM : 2 ≤ M) : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M ≤ 2 := by
  have h2 : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two
    have h' := (hasSum_nat_add_iff' 1).2 h
    simpa using h'.tsum_eq
  have h3 : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
    refine (summable_zeta M hM).tsum_le_tsum (fun m => ?_) (summable_zeta 2 le_rfl)
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hM)
  have h4 := Real.pi_lt_d2
  have h5 := Real.pi_pos
  rw [h2] at h3
  nlinarith

theorem multipliable_pos_abs_log_le (K : Type) [Field K] [NumberField K] [StarRing K]
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
      0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log 2 := by
  have hpos : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
    fun P => (euler_factor_log_bound K hK M (by omega) P.1 P.2).1
  have hpart := partial_sums_log_euler_factor_le K hK M hM
  have habs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) hpart
  have hsum : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := habs.of_abs
  have hprod : Real.exp (∑' P : {P : Ideal (𝓞 K) // P.IsMaximal},
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) = Formalism.HermitianLatticesTheory.lValEta K M :=
    Real.rexp_tsum_eq_tprod hpos hsum
  refine ⟨Real.multipliable_of_summable_log hpos hsum, ?_, ?_⟩
  · rw [← hprod]; exact Real.exp_pos _
  · rw [← hprod, Real.log_exp]
    have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
      (summable_zeta M hM).tsum_pos (fun m => by positivity) 0 (by positivity)
    calc |∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
        ≤ ∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun P :
            {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1))
            (by simpa [Real.norm_eq_abs] using habs)
      _ ≤ _ := habs.tsum_le_of_sum_le hpart
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log hz (zeta_le_two M hM)) (Nat.cast_nonneg _)

theorem lValEta_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ i : ℕ, 2 ≤ i → ((2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg K))⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta K i ∧ Formalism.HermitianLatticesTheory.lValEta K i ≤ 2 ^ (Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ _ hK i hi
  obtain ⟨-, h0, h1⟩ := multipliable_pos_abs_log_le K hK i hi
  rw [abs_le] at h1
  have h2 : (0 : ℝ) < 2 ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  constructor
  · rw [← Real.log_le_log_iff (inv_pos.2 h2) h0, Real.log_inv, Real.log_pow]
    exact h1.1
  · rw [← Real.log_le_log_iff h0 h2, Real.log_pow]
    exact h1.2

end GlobalTheory.EtaValueBound
end

