import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUnique

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E : Type} [AddCommGroup E] [Module Ω E]

section Units

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unitAt.zpow {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  obtain ⟨h0, h1, h2⟩ := hu
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_natCast]; exact pow_mem h1 n
    · rw [zpow_natCast, ← inv_pow]; exact pow_mem h2 n
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem h2 n
    · rw [zpow_neg, zpow_natCast, inv_inv]; exact pow_mem h1 n

theorem unitAt.prod {K : Type} (s : Finset K) {u : K → Ω} (hu : ∀ k ∈ s, unitAt ξ p (u k)) :
    unitAt ξ p (∏ k ∈ s, u k) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k hk => (hu k hk).1, prod_mem fun k hk => (hu k hk).2.1, ?_⟩
  rw [← Finset.prod_inv_distrib]
  exact prod_mem fun k hk => (hu k hk).2.2

theorem span_singleton_eq_of_unitAt {u : Ω} (hu : unitAt ξ p u) {e e' : E} (h : e' = u • e) :
    Submodule.span (regAt ξ p) {e'} = Submodule.span (regAt ξ p) {e} := by
  obtain ⟨h0, h1, h2⟩ := hu
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, h1⟩, h.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, h2⟩, ?_⟩
    show u⁻¹ • e' = e
    rw [h, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem unitAt_div_of_inChart {κ : Type} {x : κ → Ω} {c c' : κ} (h : InChart ξ x c p) (h' : InChart ξ x c' p) :
    unitAt ξ p (x c' / x c) :=
  ⟨div_ne_zero h'.1 h.1, h.2 c', by rw [inv_div]; exact h'.2 c⟩

end Units

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_dual {L : Lat ξ E} {p : Cpt ξ} {w : Module.Dual Ω E} :
    w ∈ L.dual p ↔ ∀ e ∈ L p, w e ∈ regAt ξ p := Iff.rfl

theorem IsFrameAt.dual {L : Lat ξ E} {r : ℕ} (b : Module.Basis (Fin r) Ω E) {p : Cpt ξ}
    (h : L.IsFrameAt b p) : L.dual.IsFrameAt b.dualBasis p := by
  refine ⟨b.dualBasis.linearIndependent, le_antisymm ?_ ?_⟩
  · intro w hw
    have hb : ∀ i, w (b i) ∈ regAt ξ p := fun i =>
      mem_dual.1 hw (b i) (by rw [h.2]; exact Submodule.subset_span ⟨i, rfl⟩)
    have hsum : w = ∑ i, w (b i) • b.dualBasis i := by
      simpa [Module.Basis.coe_dualBasis] using (b.sum_dual_apply_smul_coord w).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (⟨w (b i), hb i⟩ : regAt ξ p)
      (Submodule.subset_span ⟨i, rfl⟩ : b.dualBasis i ∈ Submodule.span (regAt ξ p) (Set.range b.dualBasis))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine mem_dual.2 fun e he => ?_
    rw [h.2] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.dualBasis_apply_self]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : (b.dualBasis i) (a • x) = (a : Ω) * (b.dualBasis i) x := by
        rw [show a • x = (a : Ω) • x from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem a.2 hx

theorem IsVBOn.dual {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} (h : L.IsVBOn T r ⊤) : L.dual.IsVBOn T r ⊤ := by
  intro p hp
  obtain ⟨U, hU, b, hb, hq⟩ := h p hp
  have hli := (hq p hp hU).1
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hb.ge
  have hB : ⇑B = b := Module.Basis.coe_mk hli hb.ge
  refine ⟨U, hU, B.dualBasis, B.dualBasis.span_eq, fun q hqT hqU => ?_⟩
  exact IsFrameAt.dual B (by rw [hB]; exact hq q hqT hqU)

end Lat

section Pull

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}

theorem Dominates.map_genPt (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  let pt' : Spec (CommRingCat.of Ω') := IsLocalRing.closedPoint Ω'
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  have h1 : (ξ' ≫ f) pt' = (Spec.map (CommRingCat.ofHom i) ≫ ξ) pt' :=
    congrArg (fun g : Spec (CommRingCat.of Ω') ⟶ X => g pt') h
  have h2 : (Spec.map (CommRingCat.ofHom i)) pt' = pt :=
    (inferInstance : Subsingleton (PrimeSpectrum Ω)).elim _ _
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2] at h1
  exact h1

theorem Dominates.specializes (h : Dominates ξ' ξ f i) (p' : Cpt ξ') : genPt ξ ⤳ f p'.1 := by
  rw [← h.map_genPt]
  exact p'.2.map f.continuous

theorem Lat.pull_apply {F : Type} [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (h : Dominates ξ' ξ f i)
    (j : E →+ F) (p' : Cpt ξ') :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, h.specializes p'⟩ : Set E)) := by
  show Submodule.span _ _ = _
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨h.specializes p', e, he, rfl⟩

end Pull

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_of_chart_generators {κ : Type} {x : κ → Ω} (cov : ∀ p : Cpt ξ, ∃ c, InChart ξ x c p) (g : κ → E)
    (hg : ∀ (p : Cpt ξ) (c c' : κ), InChart ξ x c p → InChart ξ x c' p →
      Submodule.span (regAt ξ p) {g c'} = Submodule.span (regAt ξ p) {g c}) :
    ∃ L : Lat ξ E, ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → L p = Submodule.span (regAt ξ p) {g c} :=
  ⟨fun p => Submodule.span (regAt ξ p) {g (cov p).choose}, fun p c hc => hg p c _ hc (cov p).choose_spec⟩

theorem isVB_one_of_chart_generators {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (h : CoordTie o ξ x) {L : Lat ξ E} {g : κ → E} {V : Submodule Ω E}
    (hL : ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → L p = Submodule.span (regAt ξ p) {g c})
    (h0 : ∀ c, x c ≠ 0 → g c ≠ 0) (hV : ∀ c, x c ≠ 0 → Submodule.span Ω {g c} = V) : L.IsVB 1 V := by
  intro p _
  obtain ⟨c, hc⟩ := h.cover p
  obtain ⟨U, -, hU⟩ := h.affine c hc.1
  refine ⟨U, (hU p.1).2 ⟨p.2, hc⟩, fun _ => g c, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · rw [Set.range_const, hV c hc.1]
  · exact LinearIndependent.of_subsingleton 0 (h0 c hc.1)
  · obtain ⟨hs, hq'⟩ := (hU q.1).1 hq
    rw [hL q c hq', Set.range_const]

section Multi

variable {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω}

theorem block_ratio_mem {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h2 := h.2 (Function.update c k i)
  have e1 : ∏ k', y ⟨k', c k'⟩ = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
    (Finset.mul_prod_erase _ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)).symm
  have e2 : ∏ k', y ⟨k', Function.update c k i k'⟩ = y ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [← Finset.mul_prod_erase _ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 := by
    intro h0
    exact h.1 (by show ∏ k', y ⟨k', c k'⟩ = 0; rw [e1, h0, mul_zero])
  simp only [e1, e2] at h2
  rwa [mul_div_mul_right _ _ hP] at h2

theorem block_coord_ne_zero {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

end Multi

section Single

variable {κ : Type} {x : κ → Ω}

theorem exists_line {o : Type} [CommRing o] [Algebra o Ω] (h : CoordTie o ξ x) (d : ℕ) :
    ∃ L : Lat ξ Ω, ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → L p = Submodule.span (regAt ξ p) {x c ^ d} :=
  exists_of_chart_generators h.cover (fun c => x c ^ d) fun _ c c' hc hc' =>
    span_singleton_eq_of_unitAt ((unitAt_div_of_inChart hc hc').zpow (d : ℤ)) (by
      rw [zpow_natCast, div_pow, smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc.1)])

theorem isVB_line {o : Type} [CommRing o] [Algebra o Ω] (h : CoordTie o ξ x) {d : ℕ} {L : Lat ξ Ω}
    (hL : ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → L p = Submodule.span (regAt ξ p) {x c ^ d}) :
    L.IsVB 1 ⊤ :=
  isVB_one_of_chart_generators h hL (fun _ hc => pow_ne_zero _ hc) fun c hc => by
    refine eq_top_iff.2 fun z _ => Submodule.mem_span_singleton.2 ⟨z / x c ^ d, ?_⟩
    rw [smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc)]

end Single

end Lat

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairingStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_derivation_pairing : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | exact GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_iff_chart_localization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction | exact GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_noetherian_model_noetherian : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtTranslateStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t → ∀ (f : T → FractionRing R) (g : Γ.G.left), Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem regularAt_forall_iff_exists_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t :=
  PositivityTheory.HtPt.Unc.reg_iff

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLatticeLocalFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_lattice_local_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend | exact GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem section_eq_zero_of_val_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 :=
  PositivityTheory.HtPt.Unc.sec_inj

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar.SncBase

def SncPts {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : ℕ)
    (B : Set (Cpt ξ)) : Prop :=
  ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)

end GlobalTheory.CompanionTheory.Ar.GeoModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valAt_comp_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) → ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | exact GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_lift_existsUnique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), CoordTie ℤ ξ x → ∀ (C : Type) [Field C] (V : ValuationSubring C) (zC : Spec (CommRingCat.of C) ⟶ X), genPt ξ ⤳ centre zC → ∃! z : Spec (CommRingCat.of V) ⟶ X, genPt ξ ⤳ centre z ∧ Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coord_point_extends | exact GlobalTheory.CompanionTheory.Ar.coord_point_extends | (intros; apply GlobalTheory.CompanionTheory.Ar.coord_point_extends <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEqSpanOfIsFrameAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.wedge_eq_span_of_isFrameAt :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p →
      L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} := by
  intro X Ω _ ξ E _ _ L r b p h
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨v, hv, rfl⟩
    have hc : ∀ i, ∃ c : Fin r → regAt ξ p, ∑ j, c j • b j = v i := fun i => by
      have := hv i
      rw [h.2] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using hc
    have hv' : v = fun i => ∑ j, ((c i j : Ω)) • b j := by
      funext i
      rw [← hc i]
      rfl
    have hsum : exteriorPower.ιMulti Ω r v =
        ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
      rw [hv']
      have := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
        (fun i j => ((c i j : Ω)) • b j)
      refine this.trans (Finset.sum_congr rfl fun f _ => ?_)
      have h2 := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
        (fun i => (c i (f i) : Ω)) (fun i => b (f i))
      refine h2.trans ?_
      have h3 : ((∏ i, c i (f i) : regAt ξ p) : Ω) = ∏ i, (c i (f i) : Ω) := by simp
      rw [← h3]
      rfl
    rw [SetLike.mem_coe, hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h4 := (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, h4]
      have hm := Submodule.mem_span_singleton_self (R := regAt ξ p) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  · refine Submodule.span_mono ?_
    rintro w rfl
    refine ⟨b, fun i => ?_, rfl⟩
    rw [h.2]
    exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

