import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0319
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenus
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0317
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ExtContRep

theorem comp_rep_ae_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Set G) (hΓ : Γ.Countable) (D : Set G) (hD : MeasurableSet D)
    (r : G → G) (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ r y ∈ D) (F f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (h : F =ᵐ[μ.restrict D] f) :
    (fun y => F (r y)) =ᵐ[μ] f := by
  have h1 : ∀ᵐ x ∂μ, x ∈ D → F x = f x := (ae_restrict_iff' hD).1 h
  have h2 : ∀ᵐ x ∂μ, ∀ γ ∈ Γ, γ * x ∈ D → F (γ * x) = f (γ * x) :=
    (ae_ball_iff hΓ).2 fun γ _ => (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with x hx
  obtain ⟨γ, hγ, e, hm⟩ := hr x
  rw [e] at hm ⊢
  rw [hx γ hγ hm, hf γ hγ]

theorem ae_ae_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [SFinite μ] [SFinite ν] (p : G → Prop) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, p (m * x) := by
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h0 : ∀ᵐ x ∂μ, x ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  have hm : MeasurableSet {z : G × G | z.2 * z.1 ∉ Z} :=
    (measurable_snd.mul measurable_fst) hZm.compl
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z :=
    (Measure.ae_ae_comm (p := fun x m => m * x ∉ Z) hm).2
      (Filter.Eventually.of_forall fun m =>
        (measurePreserving_mul_left μ m).quasiMeasurePreserving.ae h0)
  filter_upwards [h1] with x hx
  filter_upwards [hx] with m hmx
  by_contra hp
  exact hmx (hZ hp)

theorem ext_ae_eq_contRep : ∀ (B : RowsAut) (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B y f → B.I.ext y =ᵐ[B.I.muA B.μf] f ∧ (∀ f', IsContRep B y f' → f' = f) ∧ (∀ g, IsContRep B (B.R g y) (fun x => f (x * g))) ∧ ∀ ν : Measure B.I.GA, IsFiniteMeasure ν → ∀ᵐ x ∂(B.I.muA B.μf), ∀ᵐ m ∂ν, B.I.ext y (m * x) = f (m * x) := by
  intro B y f hf
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓ, hc, -, -⟩ := GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hl, hrt, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : (B.I.muA B.μf).IsMulRightInvariant := ⟨hrt⟩
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  have : SFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hcount : B.I.GFset.Countable := by
    rw [← hΓ]; exact Set.countable_coe_iff.1 hc
  have hr : ∀ z, ∃ γ ∈ B.I.GFset, B.I.rep B.fund z = γ * z ∧ B.I.rep B.fund z ∈ B.fund := by
    intro z
    have h := B.fund_spec.2.1 z
    have e : B.I.rep B.fund z = h.choose * z := by
      unfold AutInst.rep; exact dif_pos h
    exact ⟨h.choose, h.choose_spec.1, e, e ▸ h.choose_spec.2⟩
  have key : ∀ f', IsContRep B y f' → B.I.ext y =ᵐ[B.I.muA B.μf] f' := fun f' hf' =>
    comp_rep_ae_eq (B.I.muA B.μf) _ hcount _ B.fund_spec.1 _ hr _ f' hf'.2.1 hf'.2.2
  refine ⟨key f hf, fun f' hf' => ?_, fun g => ⟨?_, ?_, ?_⟩, fun ν hν => ?_⟩
  · exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hf'.1 hf.1).1 ((key f' hf').symm.trans (key f hf))
  · exact hf.1.comp (continuous_id.mul continuous_const)
  · intro γ hγ x
    simp only [mul_assoc]
    exact hf.2.1 γ hγ _
  · refine (B.R_spec g y).trans (ae_restrict_of_ae ?_)
    exact (measurePreserving_mul_right (B.I.muA B.μf) g).quasiMeasurePreserving.ae (key f hf)
  · exact ae_ae_mul (B.I.muA B.μf) ν (fun x => B.I.ext y x = f x) (key f hf)

end GlobalTheory.ExtContRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectors
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ToC

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ}

def swapEs (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) : LocNG.FrameD H r :=
  ⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ LocNG.img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [LocNG.img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * k) Λ = LocNG.img g (LocNG.img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

lemma pair_eq (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) (a : Fin r) : H.h (n (Fr.f b)) (es₂ a) = H.h (n (Fr.f b)) (Fr.es a) := by
  obtain ⟨A, -, hA⟩ := (GlobalTheory.LocOver.UnipOnto.unipotent_onto M hM H r Fr hT).2.1 n hn
  have hb : ∀ c, H.h (Fr.f c) (es₂ a) = H.h (Fr.f c) (Fr.es a) := by
    intro c
    induction c using Fin.lastCases with
    | last =>
      have e1 : H.h (Fr.f (Fin.last r)) (es₂ a) = M.L.cj (H.h (es₂ a) (Fr.f (Fin.last r))) := H.h_herm _ _
      have e2 : H.h (Fr.f (Fin.last r)) (Fr.es a) = M.L.cj (H.h (Fr.es a) (Fr.f (Fin.last r))) := H.h_herm _ _
      rw [e1, e2, h3, Fr.h_sz]
    | cast i => rw [h2, Fr.h_es]
  rw [show n (Fr.f b) = _ from hA b, h_sum_left, h_sum_left]
  exact Finset.sum_congr rfl fun c _ => by rw [hb c]

lemma pulled (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (he : ∀ x y, S.h (e x) (e y) = H.h x y)
    (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hg : ∀ a, g a = e (f a))
    (hdual : ∀ a j, hf M.L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hiso : ∀ i j, hf M.L S.Hm (gs i) (gs j) = 0) :
    (∀ i j, H.h (e.symm (gs i)) (e.symm (gs j)) = 0) ∧
    (∀ i j : Fin r, H.h (f i.castSucc) (e.symm (gs j)) = if i = j then 1 else 0) ∧
    (∀ i, H.h (e.symm (gs i)) (f (Fin.last r)) = 0) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [← he, e.apply_symm_apply, e.apply_symm_apply]; exact hiso i j
  · rw [← he, e.apply_symm_apply, ← hg]
    change hf M.L S.Hm _ _ = _
    rw [hdual]; simp [Fin.castSucc_inj]
  · rw [H.h_herm, ← he, e.apply_symm_apply, ← hg]
    change M.L.cj (hf M.L S.Hm _ _) = _
    rw [hdual]
    have : Fin.last r ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
    simp [this]

variable {P : LocNG.FPair H r} {S : Frames M.L r k}

def pair₂ (c : WCoord P S) : LocNG.FPair H r :=
  ⟨swapEs P.A (fun a => c.e.symm (S.es a))
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.2,
    swapEs P.B (fun a => c.e.symm (S.es' a))
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.2⟩

def coord₂ (c : WCoord P S) : Coord (pair₂ c) S :=
  ⟨c.e, c.h_eq, c.f_eq, c.f'_eq, fun a => (c.e.apply_symm_apply _).symm,
    fun a => (c.e.apply_symm_apply _).symm, c.T_eq, c.T'_eq, c.gg_none, c.gg_some⟩

def datEq (c : WCoord P S) : LocNG.Datum P ≃ LocNG.Datum (pair₂ c) where
  toFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  invFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem std_swap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0) (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0) (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0), Fr.T ≠ 0 → ∀ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L → ∃ m ∈ Fr.N, (∀ b, m (Fr.f b) = Fr.f b) ∧ (⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ : LocNG.FrameD H r).LamStd L = LocNG.img m (Fr.LamStd L) :=
  GlobalTheory.T.standardLattice_dualVectors_change_unipotent

lemma inv_fix {m : V ≃ₗ[E] V} {x : V} (hx : m x = x) : m⁻¹ x = x := by
  conv_lhs => rw [← hx]
  show (m⁻¹ * m) x = x
  rw [inv_mul_cancel]; rfl

lemma side_iff (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) (f : Fin (r + 1) → V) (Λ : Submodule M.L.O V) :
    (∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = LocNG.img n (Fr.LamStd L)) ↔
      ∃ n ∈ (swapEs Fr es₂ h1 h2 h3).N, f = (fun b => n ((swapEs Fr es₂ h1 h2 h3).f b)) ∧
        Λ = LocNG.img n ((swapEs Fr es₂ h1 h2 h3).LamStd L) := by
  obtain ⟨m, hm, hmf, hmΛ⟩ := std_swap M hM H r Fr es₂ h1 h2 h3 hT L hL
  have e : (swapEs Fr es₂ h1 h2 h3).LamStd L = LocNG.img m (Fr.LamStd L) := hmΛ
  rw [e]
  constructor
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m⁻¹, Fr.N.mul_mem hn (Fr.N.inv_mem hm), ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m⁻¹ (Fr.f b)); rw [inv_fix (hmf b)]
    · rw [← img_mul, mul_assoc, inv_mul_cancel, mul_one]; exact hΛ
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m, Fr.N.mul_mem hn hm, ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m (Fr.f b)); rw [hmf b]
    · rw [img_mul]; exact hΛ

end

theorem changed_duals : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have hTA : P.A.T ≠ 0 := by rw [← c.T_eq]; exact S.T.ne_zero
  have hTB : P.B.T ≠ 0 := by rw [← c.T'_eq]; exact S.T'.ne_zero
  have pA := pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso
  have pB := pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso'
  have kA : ∀ n ∈ P.A.N, ∀ b a, H.h (n ((pair₂ c).A.f b)) ((pair₂ c).A.es a) = H.h (n (P.A.f b)) (P.A.es a) :=
    fun n hn b a => pair_eq hM P.A _ pA.1 pA.2.1 pA.2.2 hTA hn b a
  have kB : ∀ n ∈ P.B.N, ∀ b a, H.h (n ((pair₂ c).B.f b)) ((pair₂ c).B.es a) = H.h (n (P.B.f b)) (P.B.es a) :=
    fun n hn b a => pair_eq hM P.B _ pB.1 pB.2.1 pB.2.2 hTB hn b a
  refine ⟨pair₂ c, coord₂ c, datEq c, rfl, rfl, ?_, rfl, rfl, Iff.rfl, fun d => rfl, ?_, ?_, fun g d d' => Iff.rfl⟩
  · unfold LocNG.FPair.K0
    congr 1
    ext s
    constructor
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [← kA s hs'.1 b a, ← kB s hs'.2 b a]
      exact h a b
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [kA s hs'.1 b a, kB s hs'.2 b a]
      exact h a b
  · intro d t
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (side_iff hM P.A _ pA.1 pA.2.1 pA.2.2 hTA d.L d.hL t.f t.abelian₂)
        (and_congr (side_iff hM P.B _ pB.1 pB.2.1 pB.2.2 hTB d.L' d.hL' t.f' t.abelian₂) Iff.rfl)))
  · rintro d t ⟨-, -, ⟨n, hn, hf, -⟩, ⟨n', hn', hf', -⟩, -⟩
    have e1 : (pair₂ c).A.coefSum t.f = P.A.coefSum t.f := by
      unfold LocNG.FrameD.coefSum; rw [hf]
      exact Finset.sum_congr rfl fun a _ => kA n hn a.succ a
    have e2 : (pair₂ c).B.coefSum t.f' = P.B.coefSum t.f' := by
      unfold LocNG.FrameD.coefSum; rw [hf']
      exact Finset.sum_congr rfl fun a _ => kB n' hn' a.succ a
    unfold LocNG.om LocNG.FrameD.psiOf
    rw [e1, e2]

end GlobalTheory.HL.ToC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainCovol
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

theorem fundamentalDomain_covol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K : Subgroup (HA (AF F) σ J), IsClosed (K : Set (HA (AF F) σ J)) → ∀ μ : Measure K, μ.IsHaarMeasure → (∃ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) ∧ (∀ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ → covol μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧ ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ ratOf (K := K), ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧ ∀ c : NNReal, c ≠ 0 → covol (c • μ) = (c : ℝ) * covol μ := by
  intro F E _ _ _ _ _ σ _ n J _ K _ μ hμ

  refine domains_and_covolume F E σ n J K (ratOf (K := K)) rfl covol ?_ μ hμ
  intro ν hν
  refine ⟨hν.choose, hν.choose_spec, ?_⟩
  rw [covol, dif_pos hν]

end GlobalTheory.ClosedSubgroupCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenusStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), (∀ y, e (star y) = star (e y)) → I'.n = I.n → Aᴴ * I.J * A = I'.J.map e → (∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)) → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure], IsGaugeAll I c → IsGaugeAll I' c' → gaugeVol I c μf = gaugeVol I' c' μf' := by
  first | exact @GlobalTheory.GaugeTransport.gaugeVol_transport | exact GlobalTheory.GaugeTransport.gaugeVol_transport | (intros; apply GlobalTheory.GaugeTransport.gaugeVol_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariantStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  first | exact @GlobalTheory.StabUnfold.gaussAt_meas_inv | exact GlobalTheory.StabUnfold.gaussAt_meas_inv | (intros; apply GlobalTheory.StabUnfold.gaussAt_meas_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantsScalarOnLowestKTypeCoefficientsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_scalar_on_lowestKType_coefficients : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ c : ℕ → ℂ, ∀ s ∈ lowKSub ε lam σ, ∀ u : H, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) ∧ ∀ m, ∀ g ∈ UJset ε, gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = c m * ⟪u, σ g s⟫_ℂ := by
  first | exact @GlobalTheory.CentreLow.centre_scalar_low | exact GlobalTheory.CentreLow.centre_scalar_low | (intros; apply GlobalTheory.CentreLow.centre_scalar_low <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbitsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  first | exact @GlobalTheory.Unfold.GlueOrbit.glue_local_orbits | exact GlobalTheory.Unfold.GlueOrbit.glue_local_orbits | (intros; apply GlobalTheory.Unfold.GlueOrbit.glue_local_orbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbitsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  first | exact @GlobalTheory.Unfold.massA_eq_sum_orbits | exact GlobalTheory.Unfold.massA_eq_sum_orbits | (intros; apply GlobalTheory.Unfold.massA_eq_sum_orbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroupStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_stable_under_rationalComplementGroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  first | exact @GlobalTheory.GenusStab.inGen_of_gRel | exact GlobalTheory.GenusStab.inGen_of_gRel | (intros; apply GlobalTheory.GenusStab.inGen_of_gRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnitaryFirstHermitianSpaceIsUnitStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ g : GL (Fin (D.R.N 0)) D.host.E, (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE := by
  first | exact @GlobalTheory.St.gramN_unitary_isUnit | exact GlobalTheory.St.gramN_unitary_isUnit | (intros; apply GlobalTheory.St.gramN_unitary_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarVolumeThinTubeUnitaryProductAsymptoticStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_volume_thin_tube_unitary_product_asymptotic : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∀ (μ : Measure (PI.MtM (k + 1))) (μ₀ : Measure (PI.MtM k)) (c c₀ : ℝ), 0 < c → 0 < c₀ → PI.IsHaarOnM (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ → HasDens (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ (ENNReal.ofReal c) → PI.IsHaarOnM (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ → μ₀ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ (ENNReal.ofReal c₀) → Tendsto (fun t : ℝ => μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  first | exact @GlobalTheory.Tube.thin_tube | exact GlobalTheory.Tube.thin_tube | (intros; apply GlobalTheory.Tube.thin_tube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenusStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattices_level_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  first | exact @GlobalTheory.St.G.tlat_one_genus | exact GlobalTheory.St.G.tlat_one_genus | (intros; apply GlobalTheory.St.G.tlat_one_genus <;> assumption)
end

