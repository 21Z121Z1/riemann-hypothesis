import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsOpenOfStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem isClosed_of_isOpen_of_stable {S : Scheme.{0}} [IsLocallyNoetherian S] {L : Set S} (ho : IsOpen L)
    (hs : ∀ t ∈ L, ∀ s, s ∈ closure ({t} : Set S) → s ∈ L) : IsClosed L := by
  rw [← closure_subset_iff_isClosed]
  intro s hsc
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hUa : IsAffineOpen U := hU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set S) := noetherianSpace_of_isAffineOpen U hUa
  haveI : QuasiSober (U : Set S) := U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  let s' : (U : Set S) := ⟨s, hsU⟩
  let L' : Set (U : Set S) := Subtype.val ⁻¹' L
  have hL'o : IsOpen L' := ho.preimage continuous_subtype_val
  have hs' : s' ∈ closure L' := by
    rw [mem_closure_iff]
    intro O hO hsO
    obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hO
    obtain ⟨x, ⟨hxO, hxU⟩, hxL⟩ := mem_closure_iff.mp hsc (O₀ ∩ U) (hO₀.inter U.isOpen) ⟨hsO, hsU⟩
    exact ⟨⟨x, hxU⟩, hxO, hxL⟩
  let D : Set (U : Set S) := ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set S) | (Z ∩ L').Nonempty}, Z
  have hD : IsClosed D :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  have hLD : L' ⊆ D := fun y hy =>
    Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, y, mem_irreducibleComponent, hy⟩
      mem_irreducibleComponent
  obtain ⟨Z, ⟨hZ, hZL⟩, hsZ⟩ := Set.mem_iUnion₂.mp ((closure_minimal hLD hD) hs')
  have hZi : IsIrreducible Z := hZ.1
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hg : IsGenericPoint hZi.genericPoint Z := by
    have := hZi.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  have hgL : hZi.genericPoint ∈ L' := (hg.mem_open_set_iff hL'o).mpr hZL
  have hsp : hZi.genericPoint ⤳ s' := by
    rw [specializes_iff_mem_closure, hg.def]; exact hsZ
  exact hs _ hgL s (specializes_iff_mem_closure.mp (hsp.map continuous_subtype_val))

theorem eqLocus_isClosedImmersion : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A B _ _ u v hA hB hu hv
  haveI := hA.comm
  haveI := hB.comm
  let P : S → Prop := fun t => ∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t
  have hloc : ∀ t, P t → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left :=
    fun t ht => eq_near_fibre_of_quot_contracts S A B u v hA hB hu hv t ht
  have hagree : ∀ V : S.Opens, (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left → ∀ t ∈ V, P t := by
    intro V hV t htV x hx
    have hxV : x ∈ A.hom ⁻¹ᵁ V := by show A.hom x ∈ V; rw [hx]; exact htV
    obtain ⟨y, rfl⟩ : x ∈ Set.range (A.hom ⁻¹ᵁ V).ι := by rw [Scheme.Opens.range_ι]; exact hxV
    let Q : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
    have hQ : Q ≫ u = Q ≫ v := by ext1; simpa [Q] using hV
    have h1 : Q ≫ (u * v⁻¹) = 1 := by rw [comp_mul, GrpObj.comp_inv, hQ, mul_inv_cancel]
    have h2 : (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left := by
      have := congrArg CommaMorphism.left h1
      simpa [Q, Hom.one_def] using this
    have e1 : ((A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left) y = (((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left) y := by
      rw [h2]
    simp only [Scheme.Hom.comp_apply] at e1
    rw [e1, hx]
  let L : Set S := {t | P t}
  have hLo : IsOpen L := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t ht
    exact ⟨V, fun t' ht' => hagree V hV t' ht', V.isOpen, htV⟩
  have hLc : IsClosed L := isClosed_of_isOpen_of_stable hLo fun t ht s hs =>
    hom_diff_unit_specialises S A B u v hA hB hu hv t s hs ht
  let W : S.Opens := ⟨L, hLo⟩
  have hWi : IsClosedImmersion W.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hLc)
  refine ⟨W, W.ι, hWi, ?_⟩
  intro T t A' _ φ' hp
  constructor
  · intro he
    have hr : Set.range t ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      exact eq_unit_of_pullback_eq S A B u v hA hB hu hv T t A' φ' hp he τ
    exact ⟨IsOpenImmersion.lift W.ι t hr, IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, hz⟩
    have hmem : ∀ y : A'.left, P (t (A'.hom y)) := by
      intro y
      have : t (A'.hom y) ∈ Set.range W.ι := ⟨z (A'.hom y), by rw [← hz, Scheme.Hom.comp_apply]⟩
      rw [Scheme.Opens.range_ι] at this
      exact this
    choose V hVt hV using fun y => hloc _ (hmem y)
    have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
    let U : A'.left → A'.left.Opens := fun y => φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)
    have hyU : ∀ y, y ∈ U y := by
      intro y
      show A.hom (φ' y) ∈ V y
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      exact hVt y
    have hU : TopologicalSpace.IsOpenCover U :=
      eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
    refine Scheme.Cover.hom_ext (Scheme.openCoverOfIsOpenCover _ U hU) _ _ fun y => ?_
    show (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ u.left = (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ v.left
    rw [← morphismRestrict_ι_assoc, ← morphismRestrict_ι_assoc, hV y]

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultiple
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.MapLaw

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem hasSubst_elim {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun i => by cases i with
    | inl i => exact hu i
    | inr i => exact hv i

theorem constantCoeff_powerSeriesEvalTwoGroups_eq_zero {c : MvPowerSeries (Fin d ⊕ Fin d) R} (hc : constantCoeff c = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : constantCoeff (at2 c u v) = 0 := by
  unfold at2
  exact constantCoeff_subst_eq_zero (hasSubst_elim hu hv)
    (fun i => by cases i with
      | inl i => exact hu i
      | inr i => exact hv i) hc

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim hu hv)]
  congr 1
  funext i
  cases i <;> rfl

theorem map_op (r : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map r (op μ u v i) = op (fun j => map r (μ j)) (fun j => map r (u j)) (fun j => map r (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups r (μ i) hu hv

theorem constantCoeff_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_powerSeriesEvalTwoGroups_eq_zero (hμ i) hu hv

end GlobalTheory.MapLaw

open GlobalTheory.MapLaw in
theorem GlobalTheory.isLaw_map_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {σ : Type} (i : σ), constantCoeff (X i : MvPowerSeries σ R) = 0 :=
    fun i => constantCoeff_X i
  have h0 : ∀ i : Fin d, constantCoeff (0 : MvPowerSeries (Fin d) R) = 0 := fun _ => map_zero _
  refine ⟨⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, ?_⟩
  · rw [constantCoeff_map, hμ.const i, map_zero]
  · funext i
    have := congrArg (map r) (congrFun hμ.unit i)
    rw [map_op r μ (fun j => hX j) h0] at this
    simpa [map_X] using this
  · have := congrArg (map r) (hμ.comm i)
    unfold swap at this ⊢
    rw [mvPowerSeriesMap_evalTwoGroups r (μ i) (fun j => hX _) (fun j => hX _)] at this
    simpa [map_X] using this
  · have hx1 : ∀ j, constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx2 : ∀ j, constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx3 : ∀ j, constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have m1 : (fun j => map r (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x1 := by
      funext j; simp [x1, map_X]
    have m2 : (fun j => map r (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x2 := by
      funext j; simp [x2, map_X]
    have m3 : (fun j => map r (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x3 := by
      funext j; simp [x3, map_X]
    funext i
    have := congrArg (map r) (congrFun hμ.assoc i)
    rw [map_op r μ (constantCoeff_op hμ.const hx1 hx2) hx3,
      map_op r μ hx1 (constantCoeff_op hμ.const hx2 hx3)] at this
    have e12 : (fun j => map r (op μ x1 x2 j)) = op (fun j => map r (μ j)) x1 x2 := by
      funext j; rw [map_op r μ hx1 hx2, m1, m2]
    have e23 : (fun j => map r (op μ x2 x3 j)) = op (fun j => map r (μ j)) x2 x3 := by
      funext j; rw [map_op r μ hx2 hx3, m2, m3]
    rw [e12, e23, m1, m3] at this
    exact this
  · intro n
    induction n with
    | zero => intro i; simp [nmul]
    | succ n ih =>
      intro i
      have hc : ∀ j, constantCoeff (nmul μ n j) = 0 := fun j => (ih j).1
      have e : ∀ (m : ℕ) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S), nmul ν (m + 1) =
          op ν (nmul ν m) (fun j => X j) := by
        intro m ν
        unfold nmul
        rw [Function.iterate_succ_apply']
      have e' : nmul μ (n + 1) = op μ (nmul μ n) (fun j => X j) := by
        unfold nmul
        rw [Function.iterate_succ_apply']
      rw [e', e]
      refine ⟨constantCoeff_op hμ.const hc (fun j => hX j) i, ?_⟩
      rw [map_op r μ hc (fun j => hX j)]
      have hn : (fun j => map r (nmul μ n j)) = nmul (fun i => map r (μ i)) n := funext fun j => (ih j).2
      rw [hn]
      simp only [map_X]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfComp
section
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DPLoc

variable {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
  [IsLocalization M S] {J : Ideal B} (δ : DividedPowers J)

include M in

theorem wellDef {u v : S} {j j' : B} (hj : j ∈ J) (hj' : j' ∈ J)
    (h : u * algebraMap B S j = v * algebraMap B S j') (n : ℕ) :
    u ^ n * algebraMap B S (δ.dpow n j) = v ^ n * algebraMap B S (δ.dpow n j') := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M u
  obtain ⟨⟨c, t⟩, hc⟩ := IsLocalization.surj M v
  simp only at ha hc
  have h1 : algebraMap B S (a * t * j) = algebraMap B S (c * s * j') := by
    simp only [map_mul, ← ha, ← hc]
    linear_combination (algebraMap B S s * algebraMap B S t) * h
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : ((m : B) * (a * t)) ^ n * δ.dpow n j = ((m : B) * (c * s)) ^ n * δ.dpow n j' := by
    rw [← δ.dpow_mul hj, ← δ.dpow_mul hj']
    congr 1
    linear_combination hm
  have h3 := congrArg (algebraMap B S) h2
  simp only [map_mul, map_pow, ← ha, ← hc, mul_pow] at h3
  have hu : IsUnit ((algebraMap B S m) ^ n * (algebraMap B S s) ^ n * (algebraMap B S t) ^ n) :=
    (((IsLocalization.map_units S m).pow n).mul ((IsLocalization.map_units S s).pow n)).mul
      ((IsLocalization.map_units S t).pow n)
  apply hu.mul_left_cancel
  linear_combination h3

include M in

theorem rep₂ {x y : S} (hx : x ∈ J.map (algebraMap B S)) (hy : y ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j j' : B), j ∈ J ∧ j' ∈ J ∧ x = u * algebraMap B S j ∧
      y = u * algebraMap B S j' := by
  obtain ⟨⟨j, s⟩, hj⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  obtain ⟨⟨j', t⟩, hj'⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hy
  simp only at hj hj'
  obtain ⟨u, hu⟩ := (IsLocalization.map_units S (s * t)).exists_left_inv
  simp only [Submonoid.coe_mul, map_mul] at hu
  refine ⟨u, t * j, s * j', J.mul_mem_left _ j.2, J.mul_mem_left _ j'.2, ?_, ?_⟩
  · rw [map_mul, ← hj]; linear_combination (-x) * hu
  · rw [map_mul, ← hj']; linear_combination (-y) * hu

include M in

theorem rep {x : S} (hx : x ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j : B), j ∈ J ∧ x = u * algebraMap B S j := by
  obtain ⟨u, j, _, hj, _, e, _⟩ := rep₂ M hx hx
  exact ⟨u, j, hj, e⟩

open Classical in

def ext (n : ℕ) (x : S) : S :=
  if h : ∃ p : S × B, p.2 ∈ J ∧ x = p.1 * algebraMap B S p.2 then
    h.choose.1 ^ n * algebraMap B S (δ.dpow n h.choose.2) else 0

include M in

theorem ext_eq (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    ext δ n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) := by
  have h : ∃ p : S × B, p.2 ∈ J ∧ u * algebraMap B S j = p.1 * algebraMap B S p.2 :=
    ⟨(u, j), hj, rfl⟩
  rw [ext, dif_pos h]
  exact (wellDef M δ hj h.choose_spec.1 h.choose_spec.2 n).symm

def dp : DividedPowers (J.map (algebraMap B S)) where
  dpow := ext δ
  dpow_null {n x} hx := by
    rw [ext, dif_neg]
    rintro ⟨p, hp, rfl⟩
    exact hx (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hp))
  dpow_zero hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_zero hj]
  dpow_one hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_one hj]
  dpow_mem hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (δ.dpow_mem hn hj))
  dpow_add hx hy := by
    obtain ⟨u, j, j', hj, hj', rfl, rfl⟩ := rep₂ M hx hy
    rw [← mul_add, ← map_add, ext_eq M δ _ _ (J.add_mem hj hj'), δ.dpow_add hj hj', map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj', ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hk : k.1 + k.2 = _), map_mul]
    ring
  dpow_mul hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [← mul_assoc, ext_eq M δ _ _ hj, ext_eq M δ _ _ hj]
    ring
  mul_dpow {m n x} hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    have := congrArg (algebraMap B S) (δ.mul_dpow (m := m) (n := n) hj)
    rw [map_mul, map_mul, map_natCast] at this
    simp only [ext_eq M δ _ _ hj]
    linear_combination u ^ (m + n) * this
  dpow_comp {m n x} hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj, ext_eq M δ _ _ (δ.dpow_mem hn hj),
      δ.dpow_comp hn hj, map_mul, map_natCast]
    ring

theorem dp_dpow (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    (dp M δ).dpow n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) :=
  ext_eq M δ n u hj

theorem isDPMorphism : IsDPMorphism δ (dp (S := S) M δ) (algebraMap B S) :=
  ⟨le_rfl, fun {n} a ha ↦ by simpa using dp_dpow M δ n (1 : S) ha⟩

theorem isNilDP (h : IsNilDP δ) : IsNilDP (dp (S := S) M δ) := by
  obtain ⟨N, h⟩ := h
  have key : ∀ l : List (ℕ × S), (∀ p ∈ l, p.2 ∈ J.map (algebraMap B S)) →
      ∃ (c : S) (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) ∧
        (l'.map Prod.fst).sum = (l.map Prod.fst).sum ∧
        (l.map fun p ↦ (dp M δ).dpow p.1 p.2).prod =
          c * algebraMap B S (l'.map fun p ↦ δ.dpow p.1 p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ ↦ ⟨1, [], by simp⟩
    | cons p l ih =>
      intro hl
      obtain ⟨c, l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (by simp [hq])
      obtain ⟨u, j, hj, e⟩ := rep M (hl p (by simp))
      refine ⟨u ^ p.1 * c, (p.1, j) :: l', ?_, by simp [h2], ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        exacts [hj, h1 q hq]
      · simp only [List.map_cons, List.prod_cons, map_mul]
        rw [h3, e, dp_dpow M δ _ _ hj]
        ring
  refine ⟨N, fun l hl hN ↦ ?_⟩
  obtain ⟨c, l', h1, h2, h3⟩ := key l hl
  rw [h3, h l' h1 (h2 ▸ hN), map_zero, mul_zero]

theorem isDPMorphism_of_comp {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'')
    (g : S →+* C) (h : IsDPMorphism δ δ'' (g.comp (algebraMap B S))) :
    IsDPMorphism (dp M δ) δ'' g := by
  refine ⟨by rw [Ideal.map_map]; exact h.1, fun {n} x hx ↦ ?_⟩
  obtain ⟨u, j, hj, rfl⟩ := rep M hx
  have hm : g (algebraMap B S j) ∈ J'' := h.1 (Ideal.mem_map_of_mem _ hj)
  have e : δ''.dpow n (g (algebraMap B S j)) = g (algebraMap B S (δ.dpow n j)) := h.2 j hj
  rw [dp_dpow M δ _ _ hj, map_mul, δ''.dpow_mul hm, e, map_mul, map_pow]

theorem exists_away : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (b : B), IsNilDP δ → ∃ δ' : DividedPowers (J.map (algebraMap B (Localization.Away b))), IsNilDP δ' ∧ IsDPMorphism δ δ' (algebraMap B (Localization.Away b)) ∧ ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : Localization.Away b →+* C), IsDPMorphism δ δ'' (g.comp (algebraMap B _)) → IsDPMorphism δ' δ'' g :=
  fun _ _ _ δ b h ↦ ⟨dp (Submonoid.powers b) δ, isNilDP _ δ h, isDPMorphism _ δ,
    fun _ _ _ δ'' g hg ↦ isDPMorphism_of_comp _ δ δ'' g hg⟩

end GlobalTheory.DPLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifference
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem isIntegral_sq_mul_wp_sub_div : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 →
      IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  intro N _ τ ω hj hω x y hx hy
  obtain ⟨hR, -, -, -, hz, -⟩ := GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N
  have hvz : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)), vact N v γ = 0 ↔ v = 0 := fun v γ => hz v _
  let ι := {p : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) // p.1 ≠ 0 ∧ p.2 ≠ 0}
  let act : ι → SL(2, ℤ) → ι := fun p γ =>
    ⟨(vact N p.1.1 γ, vact N p.1.2 γ), by simp only [ne_eq, hvz]; exact p.2⟩
  have hRA : IsRAct act :=
    ⟨fun p => Subtype.ext (Prod.ext (hR.1 _) (hR.1 _)),
     fun p γ δ => Subtype.ext (Prod.ext (hR.2 _ _ _) (hR.2 _ _ _))⟩
  have h1 : IsFam act 2 (fun p => wp N p.1.1) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.1) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have h2 : IsFam act 2 (fun p => wp N p.1.2) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.2) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have hsub := ((GlobalTheory.QFam.isFam_algebra ι act).2.1 2 _ _ h1 h2).2
  have hfam : IsFam act ((2 : ℕ) : ℤ) (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    have := (GlobalTheory.QFam.isFam_algebra ι act).2.2.1 2 ((N : ℂ) ^ 2) _ hsub
    simpa using this
  let R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  have hmem : ∀ z : ℂ, z ∈ R ↔ IsIntegral ℤ z := fun z => by
    simp [R, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  have hNx : ∀ v : Fin 2 → ZMod N, N • v = 0 := fun v => by
    funext i; simp [nsmul_eq_mul, ZMod.natCast_self]
  have hQ : ∀ p : ι, QAll (· ∈ R) N (fun τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    intro p
    refine ⟨fun n => (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n), ?_, fun n => ?_⟩
    · exact (GlobalTheory.QFam.hasQ_linear N).2.2.1 _ _ _ ((GlobalTheory.QFam.hasQ_linear N).2.1 _ _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _) (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _))
    · show (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) ∈ R
      rw [hmem]
      have e : (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) =
          (N : ℂ) ^ 2 * cB N p.1.1 n - (N : ℂ) ^ 2 * cB N p.1.2 n := by
        simp only [cP, if_neg p.2.1, if_neg p.2.2]; ring
      rw [e]
      exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.1 n (NeZero.pos N) (hNx _)).1.sub
        (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.2 n (NeZero.pos N) (hNx _)).1
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hT := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act 2 N (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) R τ ω
    (NeZero.pos N) hRA.actBij hfam hQ hjR hω ⟨(x, y), hx, hy⟩
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ ((r : ℂ)) := (hmem _).1 r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).1 h⟩
  exact isIntegral_trans _ hT

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIff
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isOpen_nz_and_mem_nz_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ h
  have key : ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
    intro i y hy
    have e := h.2 i (A.pick y) y (Set.mem_univ _) hy (A.mem_pick y)
    have g := A.g_ne Λ i (A.pick y) y hy (A.mem_pick y)
    simp only [nz, Set.mem_setOf_eq, e, ne_eq, mul_eq_zero, g, false_or]
  refine ⟨?_, key⟩
  have cont : ∀ i, ContinuousOn (τ i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (τ i ∘ (A.chart i).symm) (A.chart i).target := by
      simpa using (h.1 i).continuousOn
    have h2 := h1.comp (A.chart i).continuousOn (A.chart i).mapsTo
    refine h2.congr ?_
    intro y hy
    simp [(A.chart i).left_inv hy]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hs := (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousAt (τ (A.pick y)) y := (cont _).continuousAt hs
  have hne : τ (A.pick y) y ≠ 0 := hy
  filter_upwards [hs, hc.eventually_ne hne] with x hx hx'
  exact (key _ x hx).2 hx'

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardOneVariableExistsWittLiftStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lazard_one_variable_exists_witt_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ) (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) → (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) → ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k, t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧ WittVector.constantCoeff w = a i := by
  first | exact @GlobalTheory.LazardOne.exists_lift | exact GlobalTheory.LazardOne.exists_lift | (intros; apply GlobalTheory.LazardOne.exists_lift <;> assumption)
end

