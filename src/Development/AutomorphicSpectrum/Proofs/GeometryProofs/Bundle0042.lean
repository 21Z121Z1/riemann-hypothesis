import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameOpenNeighbourhood
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem frame_spread_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q :=
  PositivityTheory.HtPt.Mc.frame_spread

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_via_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E), CoordTie ℤ ξ x → L.IsVB r V → IsTwistGen ξ x L m φ → LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V → ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | exact GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_ratio_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | exact GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChangeStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_field_change : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | exact GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericFieldStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalIndexFrameLogNormStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_index_frame_log_norm : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L), C.det ≠ 0 → (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧ (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup = ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOnePrimeDvrStalkStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_dvr_stalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one | exact GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem exists_isFinite_open_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  refine ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart f, fun x hx => ?_⟩
  exact GlobalTheory.mem_finitePart_of_eq_closedPoint f x hx

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalEndomorphismStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_functional_endomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo | exact GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalMulStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_functional_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add | exact GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUniqueStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_functional_unique_mod_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff | exact GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmega
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtHoriz

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] {L : Type} [AddCommGroup L] [Module R L]

theorem map_add_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (a b : L) : j (a + b) = j a + j b := by
  have key : ∀ e, M.pt (j e) = LieCarrier.epsHom k x ξ hx ≫ M₀.pt e :=
    fun e => Over.OverMorphism.ext (hj e)
  apply M.inj
  rw [M.add, key, key, key, M₀.add, MonObj.comp_mul]

theorem map_smul_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (c : R) (e : L) : j (c • e) = k c • j e := by
  apply M.inj
  apply Over.OverMorphism.ext
  rw [hj, M₀.smul, M.smul, hj, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, LieCarrier.dualMap_epsMul]

theorem isHT_add_natCast_smul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {i : Γ.G.left ⟶ G.left}
    {L : Type} [AddCommGroup L] [Module R L] {M : LieModel G x L} {N : ℕ} {χ : T →* Rˣ}
    {w : Module.Dual R L} (h : Γ.IsHT i M N χ w) (u : Module.Dual R L) :
    Γ.IsHT i M N χ (w + (N : R) • u) := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-u e, by simp⟩

theorem natCast_smul_isHTFormOver (M : LieModel G ξ E) (N : ℕ) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (hk : Function.Injective k) (h : M.IsHTFormOver N x k 0)
    (w : Module.Dual Ω E)
    (hw : ∀ (e : E) (v : epsAt x ⟶ G), IsTanAt G x v →
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → w e ∈ k.range) :
    M.IsHTFormOver N x k ((N : Ω) • w) := by
  obtain ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, ht, hj, hHT, h0⟩ := h
  have hreg : ∀ e, ∃ r, k r = w (j e) := fun e => hw (j e) (M₀.pt e) (M₀.tan e) (hj e)
  choose f hf using hreg
  let u : Module.Dual R L :=
    { toFun := f
      map_add' := fun a b => hk (by rw [map_add, hf, hf, hf, map_add_of_compat M hx M₀ j hj, map_add])
      map_smul' := fun c e => hk (by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul]
        rw [hf, hf, map_smul_of_compat M M₀ j hj, map_smul, smul_eq_mul]) }
  refine ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀ + (N : R) • u, ht, hj, isHT_add_natCast_smul Γ hHT u, fun e => ?_⟩
  have h1 : k (w₀ e) = 0 := (h0 e).symm
  have h2 : k (u e) = w (j e) := hf e
  simp [h1, h2]

end GlobalTheory.CompanionTheory.Ar.HtHoriz

namespace GlobalTheory.CompanionTheory.Ar

theorem htLat_le_omLat_and_smul_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ),
    IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧
      (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  intro X Ω _ ξ G _ _ V _ _ M N p hξ _
  refine ⟨?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
    obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
    obtain ⟨e₀, rfl⟩ := M₀.onto v hv
    have : j e₀ = e := M.inj (Over.OverMorphism.ext ((hj e₀).trans hev.symm))
    subst this
    exact ⟨w₀ e₀, (hw e₀).symm⟩
  · intro h w hw
    exact Submodule.subset_span (HtHoriz.natCast_smul_isHTFormOver M N (LieCarrier.genMap_fromSpecStalk p) (hξ.inj p) h w
      fun e v hv hev => hw e (Submodule.subset_span ⟨v, hv, hev⟩))

end GlobalTheory.CompanionTheory.Ar
end
end

