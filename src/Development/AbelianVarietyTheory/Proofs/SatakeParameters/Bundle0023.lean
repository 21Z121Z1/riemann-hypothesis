import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegralStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_adele_split_place_support_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L), Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 → ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) → Valued.v (s.proj z) ≤ 1 → Valued.v (s.proj (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 → z ∈ ReciprocityTheory.Aut.ALint L := by
  first | exact @GlobalTheory.mem_ALint_of_supported_at_split | exact GlobalTheory.mem_ALint_of_supported_at_split | (intros; apply GlobalTheory.mem_ALint_of_supported_at_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WD

theorem lpSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  intro hab
  rw [lpSum_mk, lpSum_mk, mk_eq_mk] at hab
  obtain ⟨e, h1, h2⟩ := hab
  let fa : Option (Weil h) → Module.End ℂ (Fin n → ℂ) := fun o => o.elim a.N a.ρ
  let fb : Option (Weil h) → Module.End ℂ (Fin m → ℂ) := fun o => o.elim b.N b.ρ
  let fc : Option (Weil h) → Module.End ℂ (Fin k → ℂ) := fun o => o.elim c.N c.ρ
  obtain ⟨e', he'⟩ := GlobalTheory.T.endomorphismFamily_direct_summand_cancellation ℂ (Option (Weil h)) (Fin n → ℂ) (Fin m → ℂ) (Fin k → ℂ)
    fa fb fc ⟨e, fun i x => by
      cases i with
      | none => exact h2 x
      | some σ => exact h1 σ x⟩
  exact sound ⟨e', fun σ v => he' (some σ) v, fun v => he' none v⟩

end GlobalTheory.WeilDeligne.WD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomialStatement
section
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧ ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  first | exact @GlobalTheory.LatHecke.subElem_degrees | exact GlobalTheory.LatHecke.subElem_degrees | (intros; apply GlobalTheory.LatHecke.subElem_degrees <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGaloisStatement
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w → ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  first | exact @GlobalTheory.HeckeSplit.eventually_degOne_moved | exact GlobalTheory.HeckeSplit.eventually_degOne_moved | (intros; apply GlobalTheory.HeckeSplit.eventually_degOne_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongrModPowResidueDegreeOneFactorsStatement
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  first | exact @GlobalTheory.exists_shift_mod_pow_degOne | exact GlobalTheory.exists_shift_mod_pow_degOne | (intros; apply GlobalTheory.exists_shift_mod_pow_degOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSchwartzBumpNearIdentity
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory.GodementJacquet.TestNearE

open ValuativeRel Filter Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topRows (r t : ℕ) (x : Matrix (Fin (r + t)) (Fin r) k) : Matrix (Fin r) (Fin r) k :=
  x.submatrix (Fin.castAdd t) id

theorem continuous_topRows (r t : ℕ) : Continuous (topRows (k := k) r t) :=
  Continuous.matrix_submatrix continuous_id _ _

theorem topRows_eMat_mul (r t : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    topRows r t (eMat k r t * g) = g := by
  ext i j
  simp [topRows, eMat, Matrix.mul_apply, Fin.val_inj]

theorem topRows_eMat (r t : ℕ) : topRows r t (eMat k r t) = 1 := by
  simpa using topRows_eMat_mul (k := k) r t 1

theorem isOpen_vle {δ : ValueGroupWithZero k} (hδ : δ ≠ 0) :
    IsOpen {z : k | valuation k z ≤ δ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 δ hδ, fun z hz => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hx ⊢
  calc valuation k z = valuation k ((z - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (z - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ δ := max_le hz.le hx

theorem isCompact_vle_sub (δ : ValueGroupWithZero k) (c : k) :
    IsCompact {z : k | valuation k (z - c) ≤ δ} := by
  have h := (IsNonarchimedeanLocalField.isCompact_closedBall k δ).image (continuous_add_right c)
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨z - c, hz, sub_add_cancel z c⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem exists_nhds_one (r : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ W ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) k), ∀ g : GL (Fin r) k, g.val ∈ W → g ∈ S := by
  obtain ⟨U, hU, hUS⟩ := (Units.isEmbedding_embedProduct (M := Matrix (Fin r) (Fin r) k)).isInducing.isOpen_iff.mp hS
  let φ : Matrix (Fin r) (Fin r) k → Matrix (Fin r) (Fin r) k × (Matrix (Fin r) (Fin r) k)ᵐᵒᵖ :=
    fun x => (x, MulOpposite.op x⁻¹)
  have hφ : ContinuousAt φ 1 := by
    refine continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp ?_)
    apply continuousAt_matrix_inv
    rw [Matrix.det_one, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hemb : ∀ g : GL (Fin r) k, Units.embedProduct _ g = φ g.val := by
    intro g
    simp [φ, Units.embedProduct_apply, Matrix.coe_units_inv]
  refine ⟨φ ⁻¹' U, hφ.preimage_mem_nhds (hU.mem_nhds ?_), fun g hg => ?_⟩
  · have : (1 : GL (Fin r) k) ∈ Units.embedProduct _ ⁻¹' U := by rw [hUS]; exact h1
    simpa [hemb] using this
  · rw [← hUS]
    show Units.embedProduct _ g ∈ U
    rw [hemb]; exact hg

end GlobalTheory.GodementJacquet.TestNearE

namespace GlobalTheory.GodementJacquet.TestNearE

open ValuativeRel Filter Topology

theorem nhds_zero_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) : (𝓝 (0 : Matrix (Fin n) (Fin m) k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by
  have h0 := IsValuativeTopology.hasBasis_nhds_zero k
  have h1 : (𝓝 (0 : Fin m → k)).HasBasis (fun Ik : Set (Fin m) × (ValueGroupWithZero k)ˣ => Ik.1.Finite ∧ True)
      (fun Ik => Ik.1.pi fun _ => {x : k | valuation k x < Ik.2}) := by
    rw [nhds_pi]; exact h0.pi_self
  have h2 : (𝓝 (0 : Fin n → Fin m → k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by
    rw [nhds_pi]; exact h1.pi_self
  exact h2

theorem exists_test (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  set e := eMat k r t
  obtain ⟨W, hW, hWS⟩ := exists_nhds_one r S hS h1
  have hP : topRows r t ⁻¹' W ∈ 𝓝 e :=
    (continuous_topRows (k := k) r t).continuousAt.preimage_mem_nhds (by rw [topRows_eMat]; exact hW)
  have hP' : (fun y => y + e) ⁻¹' (topRows r t ⁻¹' W) ∈ 𝓝 (0 : Matrix (Fin (r + t)) (Fin r) k) :=
    (continuous_add_right e).continuousAt.preimage_mem_nhds (by rw [zero_add]; exact hP)
  obtain ⟨⟨I, J, γ⟩, -, hsub⟩ := (nhds_zero_basis k (r + t) r).mem_iff.mp hP'
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set δ : ValueGroupWithZero k := (γ : ValueGroupWithZero k) * valuation k ϖ
  have hδ0 : δ ≠ 0 := mul_ne_zero γ.ne_zero (by simpa using hϖ0)
  have hδγ : δ < γ := mul_lt_of_lt_one_right (zero_lt_iff.mpr γ.ne_zero) hϖ1
  set N : Set (Matrix (Fin (r + t)) (Fin r) k) := {x | ∀ i j, valuation k (x i j - e i j) ≤ δ}
  have hNpi : N = Set.pi Set.univ fun i => Set.pi Set.univ fun j => {z : k | valuation k (z - e i j) ≤ δ} :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  have hNc : IsCompact N := by
    rw [hNpi]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_vle_sub δ (e i j)
  have hNo : IsOpen N := by
    have : N = ⋂ i, ⋂ j, (fun x : Matrix (Fin (r + t)) (Fin r) k => x i j - e i j) ⁻¹' {z : k | valuation k z ≤ δ} := by
      ext x; simp [N]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_vle hδ0).preimage ((Continuous.matrix_elem continuous_id i j).sub continuous_const)
  have hNcl : IsClosed N := hNc.isClosed
  have heN : e ∈ N := fun i j => by simp
  have hNP : ∀ x ∈ N, topRows r t x ∈ W := by
    intro x hx
    have : x - e ∈ I.pi fun _ => J.pi fun _ => {z : k | valuation k z < γ} :=
      fun i _ j _ => lt_of_le_of_lt (by simpa using hx i j) hδγ
    simpa using hsub this
  classical
  refine ⟨N.indicator 1, ⟨?_, ?_⟩, by simp [heN], fun x => ?_, fun g hg => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ N
    · exact ⟨N, hNo, hx, fun y hy => by simp [hx, hy]⟩
    · exact ⟨Nᶜ, hNcl.isOpen_compl, hx, fun y hy => by simp [hx, Set.indicator_of_notMem hy]⟩
  · exact HasCompactSupport.intro' hNc hNcl fun x hx => Set.indicator_of_notMem hx _
  · by_cases hx : x ∈ N <;> simp [hx]
  · have hm : e * g.val ∈ N := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    have := hNP _ hm
    rw [topRows_eMat_mul] at this
    exact hWS g this

end GlobalTheory.GodementJacquet.TestNearE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

def FibrePointsLE {Z X : Scheme.{0}} (f : Z ⟶ X) (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) (s : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z)),
    (∀ j, s j ≫ f = y) → ¬ Function.Injective s

def diagCompl {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f))ᶜ, (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

def diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (diagCompl f).toScheme ⟶ Z :=
  (diagCompl f).ι ≫ pullback.snd f f

end GlobalTheory.EtC.Tr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomExtOfCovering
section
open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

theorem freePresheaf_map_app_freeMk (R : Type) [CommRing R] {P Q : Scheme.{0}ᵒᵖ ⥤ Type} (α : P ⟶ Q) (U : Scheme.{0}ᵒᵖ)
    (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).map α).app U) (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (α.app U x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ Type) {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V)
    (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).obj P).map f) (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map f x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_map_comp_app_freeMk (R : Type) [CommRing R] {P Q : Scheme.{0}ᵒᵖ ⥤ Type}
    {G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (α : P ⟶ Q) (β : (GlobalTheory.EtC.freeP R).obj Q ⟶ G)
    (U : Scheme.{0}ᵒᵖ) (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).map α ≫ β).app U) (ModuleCat.freeMk (ULift.up x)) =
      ConcreteCategory.hom (β.app U) (ModuleCat.freeMk (ULift.up (α.app U x))) :=
  congrArg (ConcreteCategory.hom (β.app U)) (freePresheaf_map_app_freeMk R α U x)

theorem freePresheaf_hom_naturality_freeMk (R : Type) [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ Type}
    {G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (β : (GlobalTheory.EtC.freeP R).obj P ⟶ G)
    {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (x : P.obj U) :
    ConcreteCategory.hom (G.map f) (ConcreteCategory.hom (β.app U) (ModuleCat.freeMk (ULift.up x))) =
      ConcreteCategory.hom (β.app V) (ModuleCat.freeMk (ULift.up (P.map f x))) := by
  have h := ConcreteCategory.congr_hom (β.naturality f) (ModuleCat.freeMk (ULift.up x))
  exact h.symm.trans (congrArg (ConcreteCategory.hom (β.app V)) (freePresheaf_obj_map_freeMk R P f x))

end GlobalTheory.EtC.Tr

namespace GlobalTheory.EtC.Tr

theorem free_hom_ext_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R)
    (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S) (hT : T ∈ Scheme.etaleTopology S)
    (h : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v →
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) : φ = ψ := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((GlobalTheory.EtC.freeP R).obj (yoneda.obj S)) F).injective
  have key : ∀ ⦃W : Scheme.{0}⦄ (v : W ⟶ S), T v →
      ConcreteCategory.hom ((adj.homEquiv _ F φ).app (op W)) (ModuleCat.freeMk (ULift.up v)) =
      ConcreteCategory.hom ((adj.homEquiv _ F ψ).app (op W)) (ModuleCat.freeMk (ULift.up v)) := by
    intro W v hv
    have e : ∀ χ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F,
        adj.homEquiv _ F ((GlobalTheory.EtC.free R).map (yoneda.map v) ≫ χ) =
          (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F χ := fun χ =>
      adj.homEquiv_naturality_left _ _
    have h' : (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F φ =
        (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F ψ := by
      rw [← e φ, ← e ψ]; exact congrArg (adj.homEquiv _ F) (h v hv)
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app h' (op W)) (ModuleCat.freeMk (ULift.up (𝟙 W)))
    rw [freePresheaf_map_comp_app_freeMk, freePresheaf_map_comp_app_freeMk] at h1
    have hv1 : ConcreteCategory.hom ((yoneda.map v).app (op W)) (𝟙 W) = v := Category.id_comp v
    rw [hv1] at h1
    exact h1
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨g⟩
  apply Sheaf.isSeparated F U.unop (T.pullback g) (Scheme.etaleTopology.pullback_stable g hT)
  intro W w hw
  have nat : ∀ χ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F,
      ConcreteCategory.hom (F.obj.map w.op) (ConcreteCategory.hom ((adj.homEquiv _ F χ).app U)
        (ModuleCat.freeMk (ULift.up g))) =
        ConcreteCategory.hom ((adj.homEquiv _ F χ).app (op W)) (ModuleCat.freeMk (ULift.up (w ≫ g))) :=
    fun χ => freePresheaf_hom_naturality_freeMk R (adj.homEquiv _ F χ) w.op g
  exact (nat φ).trans ((key (w ≫ g) hw).trans (nat ψ).symm)

end GlobalTheory.EtC.Tr

example : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S), T ∈ Scheme.etaleTopology S → (∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) → φ = ψ :=
  @GlobalTheory.EtC.Tr.free_hom_ext_of_covering
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomGlueOfCovering
section
open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

theorem free_hom_glue_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S)
    (hT : T ∈ Scheme.etaleTopology S)
    (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F))
    (hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) :
    ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v),
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by

  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) T.arrows := fun V v hv =>
    Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))

  have hres : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.res g (Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [map_res, freeGen_res]
    congr 2
  have hcomp : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.map (σ (g ≫ v) (T.downward_closed hv g)) (freeGen R (yoneda.obj W) W (𝟙 W)) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [← hσ v hv g]
    change Sec.map (σ v hv) (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map g)) (freeGen R (yoneda.obj W) W (𝟙 W))) = _
    rw [freeGen_map]
    congr 2
  have hx : x.SieveCompatible := by
    intro V W v g hv
    exact (hcomp v hv g).trans (hres v hv g).symm
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.cond)
  obtain ⟨s, hs, -⟩ := hF T hT x ((Presieve.compatible_iff_sieveCompatible x).2 hx)
  obtain ⟨t, ht⟩ := free_exists (R := R) (yoneda.obj S) F (fun U g => Sec.res g (show Sec F S from s))
    (fun V U g h => by
      change Sec.res g (Sec.res h _) = Sec.res (g ≫ h) _
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply])
  refine ⟨t, fun V v hv => ?_⟩
  apply free_ext
  intro U w
  change Sec.map t (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map v)) (freeGen R (yoneda.obj V) U w)) = _
  rw [freeGen_map, ht, ← hres v hv w]
  have hsv : Sec.res v (show Sec F S from s) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V)) := hs v hv
  rw [← hsv]
  change Sec.res (w ≫ v) _ = Sec.res w (Sec.res v _)
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end GlobalTheory.EtC.Tr

example : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S), T ∈ Scheme.etaleTopology S → ∀ (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F)), (∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) → ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v), (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv :=
  @GlobalTheory.EtC.Tr.free_hom_glue_of_covering
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeDoubleCoset_adicCompletion_inv_mul_integral : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F) (k : ℕ), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (a a' b b' g g' : GL (Fin n) (v.adicCompletion F)), (∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) → (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  first | exact @GlobalTheory.hecke_loc_inv_mul_int | exact GlobalTheory.hecke_loc_inv_mul_int | (intros; apply GlobalTheory.hecke_loc_inv_mul_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulRe
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory

theorem hermitianForm_norm_sq_le_re_mul_re :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  intro V _ _ Bf hsymm hpos v w
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf y x
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf x y) = Bf y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (Bf x x)
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf z (x + y) = Bf z x + Bf z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show Bf y (r • x) = starRingEnd ℂ r * Bf y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w
  change ‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h
  rw [hsymm v w, RCLike.norm_conj] at h
  rw [sq]
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConn
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Bock

variable (Q q : ℕ) (hq : q ∣ Q) (i : ℤ)

def IsRed (φ : tw Q i ⟶ (restr (ZMod.castHom hq (ZMod q))).obj (tw q i)) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map φ (twGen i ζ) = (show Sec ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)) U from twGen i ξ)

def redS : tw Q i ⟶ (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) := pick (IsRed Q q hq i)

def IsIncl (φ : (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) ⟶ tw Q i) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map φ (show Sec ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)) U from twGen i ξ) = (Q / q) • twGen i ζ

def inclS : (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) ⟶ tw Q i := pick (IsIncl Q q hq i)

def inc (E : Spc) (n : ℤ) : Ht q E n i →+ Ht Q E n i :=
  (HK.post (ZMod Q) ((chains (ZMod Q)).obj E) (inclS Q q hq i) n).comp (restrH (ZMod.castHom hq (ZMod q)) E (tw q i) n)

def IsConn {R : Type} [CommRing R] (S : ShortComplex (Shv R)) (z : Cocycle (res R S.X₃) (res R S.X₁) 1) (s : ℤˣ) : Prop :=
  ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
      CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w

end GlobalTheory.EtC.Bock

end
end

