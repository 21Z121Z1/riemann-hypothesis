import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section Cast

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}

theorem SameSp.dmin_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (castFr h.psi x) τ i = dmin X'.Gm x ⟨τ.1, h.psi.ge τ.2⟩ i := by
  rw [← h.gm]
  rfl

theorem SameSp.castFr_mem_dom (h : SameSp X' X) {x : Frame X'.Ψ r} (hx : x ∈ X'.dom) :
    castFr h.psi x ∈ X.dom := by
  have hx' : ∀ τ : X'.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X'.p0 i * (dmin X'.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (castFr h.psi x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (castFr h.psi x) τ i).re
  intro τ
  obtain ⟨hdet, hpos⟩ := hx' ⟨τ.1, h.psi.ge τ.2⟩
  refine ⟨hdet, fun i => ?_⟩
  rw [h.dmin_castFr, ← h.p0]
  exact hpos i

theorem SameSp.EF_eq (h : SameSp X' X) (u v : Fin r → E) : EF X' u v = EF X u v := by
  rw [EF_def, EF_def, h.gm, h.ka]

private theorem GL_inv_mulVec_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    ((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((ga : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem GL_mulVec_inv_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    (ga : Matrix (Fin n) (Fin n) K) *ᵥ (((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem mem_mapL_iff (ga : GL (Fin r) E) (L : Lt E r) (v : Fin r → E) :
    v ∈ mapL ga L ↔ ∃ u ∈ L, v = (ga : Matrix (Fin r) (Fin r) E) *ᵥ u := by
  unfold mapL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩

private theorem EF_mulVec_of_isUn {Y : Data E r} {ga : GL (Fin r) E} (hga : IsUn Y ga) (u v : Fin r → E) :
    EF Y ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF Y u v := by
  rw [EF_def, EF_def, hga u v]

end Cast

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X' X : Data E r) (h : SameSp X' X) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X'.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X' bas' idx' e x L y) (ga : GL (Fin r) E), IsSympl X' bas' → IsSympl X bas → x ∈ X'.dom → SelfD X' L → IsUn X ga → (∀ v, pv X' idx' x v = pv X idx (castFr h.psi x) v) → (∀ j, rowType X' (idx' j) = rowType X (idx j)) → lact ga (castFr h.psi x) ∈ X.dom ∧ (IsUnitFr X' x → IsUnitFr X (lact ga (castFr h.psi x))) ∧ SelfD X (mapL ga L) ∧ ∃ A' : AnFib X bas idx e (lact ga (castFr h.psi x)) (mapL ga L) y, (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y.s θ) ∧ (∀ θ, MeanOne X' bas' idx' x L θ → MeanOne X bas idx (lact ga (castFr h.psi x)) (mapL ga L) θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mvMap ga mk) := by
  intro E _ _ _ H Dw l Xo c _ r g X' X h bas' idx' bas idx e x L y A ga hs' hs hxm hL hga hpv hrow
  have hx₀ : castFr h.psi x ∈ X.dom := h.castFr_mem_dom hxm
  obtain ⟨-, -, L3, -, -, -, -, L8⟩ := hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ _ hx₀
  obtain ⟨-, -, L3', -, -, -, -, -⟩ := hx_laws E r X' g bas' idx' 0 hs' ⟨0, rfl⟩ x hxm
  obtain ⟨hdom1, hpv1, hunit1, hhx1⟩ := L8 ga hga
  have pvT : ∀ u, pv X idx (lact ga (castFr h.psi x)) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) =
      pv X' idx' x u := fun u => (hpv1 u).trans (hpv u).symm
  have hxeq : ∀ z w, hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x z w := by
    intro z w
    rw [hx_eq_hermForm idx, hx_eq_hermForm idx']
    have key := hermForm_eq_of_im (ThFr.Hm X bas idx (castFr h.psi x)) (ThFr.Hm X' bas' idx' x) 1 1
      (Set.range (pv X idx (castFr h.psi x))) (span_range_pv idx hs hx₀) ?_ z w
    · simpa only [_root_.one_mul] using key
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [_root_.one_mul]
      rw [← hx_eq_hermForm idx, ← hx_eq_hermForm idx', L3 a b, ← hpv a, ← hpv b, L3' a b, h.EF_eq]
  have hxT : ∀ z w, hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x z w :=
    fun z w => (hhx1 z w).trans (hxeq z w)
  have unit0 : IsUnitFr X' x → IsUnitFr X (castFr h.psi x) := by
    unfold IsUnitFr
    intro hu τ i
    rw [h.dmin_castFr]
    exact hu _ i
  have hSD : SelfD X (mapL ga L) := by
    unfold SelfD at hL ⊢
    obtain ⟨hfg, hmem⟩ := hL
    refine ⟨hfg.map _, fun v => ?_⟩
    rw [mem_mapL_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩ w hw
      obtain ⟨u', hu', rfl⟩ := (mem_mapL_iff ga L w).1 hw
      obtain ⟨k, hk⟩ := (hmem u).1 hu u' hu'
      exact ⟨k, by rw [EF_mulVec_of_isUn hga, ← h.EF_eq]; exact hk⟩
    · intro hv
      refine ⟨((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, ?_, (GL_mulVec_inv_mulVec ga v).symm⟩
      rw [hmem]
      intro u' hu'
      obtain ⟨k, hk⟩ := hv _ ((mem_mapL_iff ga L _).2 ⟨u', hu', rfl⟩)
      refine ⟨k, ?_⟩
      rw [h.EF_eq, ← EF_mulVec_of_isUn hga (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) u',
        GL_mulVec_inv_mulVec]
      exact hk
  have hT : ∀ z, (∃ v ∈ L, z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (mem_mapL_iff ga L _).2 ⟨u, hu, rfl⟩, (pvT u).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
      exact ⟨u, hu, pvT u⟩
  refine ⟨hdom1, fun hu => hunit1 (unit0 hu), hSD, ?_⟩
  have hlin : ∀ (a : 𝓞 E) (z : Fin g → ℂ),
      A.ex (fun j => rowType X (idx j) (a : E) * z j) = A.ex z ≫ Xo.univ.t.act.act a := by
    intro a z
    have hfun : (fun j => rowType X (idx j) (a : E) * z j) =
        (fun j => rowType X' (idx' j) (a : E) * z j) := funext fun j => by rw [hrow]
    rw [hfun]
    exact A.ex_lin a z
  have hnorm : ∀ v ∈ mapL ga L, ‖A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)‖ = 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    rw [GL_inv_mulVec_mulVec]
    exact A.χ_norm u hu
  refine ⟨
    { ex := A.ex
      ex_add := A.ex_add
      ex_onto := A.ex_onto
      ex_ker := fun z => (A.ex_ker z).trans (hT z)
      ex_lin := hlin
      hol := A.hol
      der := A.der
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ := fun v => A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      χ_norm := hnorm
      fr_per := ?_ }, fun θ hθ => hθ, ?_, ?_⟩
  · intro v hv j z hz
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    simp only [GL_inv_mulVec_mulVec, pvT, hxT]
    exact A.fr_per u hu j z hz
  · intro θ hθ
    unfold MeanOne at hθ ⊢
    obtain ⟨Ag, Fd, hA, hFd, hint⟩ := hθ
    refine ⟨Ag, Fd, fun z => (hA z).trans (hT z), hFd, ?_⟩
    simp only [hxT]
    exact hint
  · intro mk hmk
    unfold AnFib.Marked at hmk ⊢
    intro a ha
    rw [hmk a ha]
    show A.ex _ = A.ex _
    congr 1
    have hmv : mvMap ga mk a = (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk a := by
      simp [mvMap, Matrix.toLin'_apply]
    rw [hmv, ← Matrix.mulVec_smul, pvT]

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandardStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : GenLat E n), Λ.Unimod → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = J • Submodule.span (𝓞 E) (detSet Λ.La) ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = Submodule.map (Algebra.linearMap (𝓞 E) E) (conjI J) ∧ ∀ h : Matrix (Fin n) (Fin n) E, Submodule.span (𝓞 E) (detSet (actLat h Λ).La) = Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (Submodule.span (𝓞 E) (detSet Λ.La)) := by
  first | exact @GlobalTheory.DetIdeal.detIdeal_selfDual | exact GlobalTheory.DetIdeal.detIdeal_selfDual | (intros; apply GlobalTheory.DetIdeal.detIdeal_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatchStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_half_level_marking_exists_and_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ζ : ℂ), SelfD X L → IsMark l L mk → IsPrimitiveRoot ζ l.M → (∃ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ) ∧ (∀ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ → L ≤ LinearMap.range δ ⊔ Mfr l • L ∧ (∀ a, δ a ∈ Mfr l • L ↔ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ ga : GL (Fin r) E, IsUn X ga → IsMark l (mapL ga L) (mvMap ga mk) ∧ IsDual X l ζ (mapL ga L) (mvMap ga mk) (mvMap ga δ)) ∧ ∀ mk' δ' : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk' → IsDual X l ζ L mk' δ' → (∀ a, δ a - δ' a ∈ Mfr l • L) → ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) ∧ conjI (Mfr l) = l.Mb ∧ Mfr l * l.Mb = Ideal.span {(l.M : 𝓞 E)} ∧ ∀ n N : ℕ, 0 < N → ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y := by
  first | exact @GlobalTheory.Dict.DualMark.dual_marking | exact GlobalTheory.Dict.DualMark.dual_marking | (intros; apply GlobalTheory.Dict.DualMark.dual_marking <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem AnFib.exists_anPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  obtain ⟨-, -, -, hadj, -, hinj, hsp, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let lat : AddSubgroup (Fin g → ℂ) :=
    { carrier := {z | ∃ v ∈ L, z = pv X idx x v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, add_mem hu hv, by rw [pv, pv, pv, per_add]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by rw [pv, per_zero]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨-u, neg_mem hu, by rw [pv, pv, per_neg]; rfl⟩ }
  have hχ (v) : Function.invFun (pv X idx x) (pv X idx x v) = v := Function.leftInverse_invFun hinj v
  let Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e :=
    { e := A.ex
      lat := lat
      span := by
        rw [← (hsp L (SW.TensLat.span_of_selfD X hL)).1]
        congr 1
        ext z
        exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩⟩
      e_add := A.ex_add
      e_onto := A.ex_onto
      e_ker := A.ex_ker
      hol := fun U f => by
        obtain ⟨h1, h2⟩ := A.hol U f
        simp only [Set.mem_univ, true_and] at h1 h2
        exact ⟨h1, h2⟩
      Hm := ThFr.Hm X bas idx x
      herm := Hm_isHermitian idx hs hx
      χ := fun z => A.χ (Function.invFun (pv X idx x) z)
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ_norm := by
        rintro _ ⟨v, hv, rfl⟩
        rw [hχ]
        exact A.χ_norm v hv
      fr_per := by
        rintro _ ⟨v, hv, rfl⟩ j z hz
        rw [hχ, ← hx_eq_hermForm, ← hx_eq_hermForm]
        exact A.fr_per v hv j z hz
      lin := A.ex_lin
      adj := fun a z w => by
        rw [← hx_eq_hermForm, ← hx_eq_hermForm]
        have hb : cc (a : E) = ((H.bar a : 𝓞 E) : E) := (H.bar_eq a).symm
        have h := hadj (a : E) z w
        rw [hb] at h
        exact h
      der := A.der }
  refine ⟨Φ, fun _ => rfl, rfl, fun _ => Iff.rfl, fun z w => (hx_eq_hermForm idx x z w).symm,
    fun v _ => congrArg A.χ (hχ v), fun _ _ _ => Iff.rfl, fun k a θ => ?_⟩
  funext z
  change cexp _ * θ (z + a) = cexp _ * θ (z + a)
  congr 2
  rw [hx_eq_hermForm]
  change _ - _ * _ * hermForm (ThFr.Hm X bas idx x) a a / 2 = _
  change -(_ * _ * hermForm (ThFr.Hm X bas idx x) z a) - _ = _
  simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul, Int.cast_natCast]
  ring

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_lift_of_projective {R P V Q : Type} [CommRing R] [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup V] [Module R V] [Group Q] (act : R → Q → Q) (L : Submodule R V) (ev : P → Q) (φ : V → Q)
    (ev_add : ∀ a b, ev (a + b) = ev a * ev b) (ev_lin : ∀ (s : R) a, ev (s • a) = act s (ev a))
    (φ_add : ∀ a b, φ (a + b) = φ a * φ b) (φ_lin : ∀ (s : R) a, φ (s • a) = act s (φ a))
    (onto : ∀ a, ∃ v ∈ L, ev a = φ v) : ∃ mk : P →ₗ[R] V, ∀ a, mk a ∈ L ∧ ev a = φ (mk a) := by
  have hev0 : ev 0 = 1 := mul_left_cancel (a := ev 0) (by rw [_root_.mul_one, ← ev_add, add_zero])
  have hφ0 : φ 0 = 1 := mul_left_cancel (a := φ 0) (by rw [_root_.mul_one, ← φ_add, add_zero])

  let W : Submodule R (P × L) :=
    { carrier := {x | ev x.1 = φ (x.2 : V)}
      add_mem' := by
        rintro ⟨a, v⟩ ⟨b, w⟩ ha hb
        simp only [Set.mem_ofPred_eq, Prod.mk_add_mk, Submodule.coe_add] at *
        rw [ev_add, φ_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero]
        rw [hev0, hφ0]
      smul_mem' := by
        rintro s ⟨a, v⟩ ha
        simp only [Set.mem_ofPred_eq, Prod.smul_mk, Submodule.coe_smul] at *
        rw [ev_lin, φ_lin, ha] }
  let f : W →ₗ[R] P := (LinearMap.fst R P L).comp W.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv, he⟩ := onto a
    exact ⟨⟨(a, ⟨v, hv⟩), he⟩, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨L.subtype.comp ((LinearMap.snd R P L).comp (W.subtype.comp h)), fun a => ⟨((h a : W) : P × L).2.2, ?_⟩⟩
  have h1 : ((h a : W) : P × L).1 = a := LinearMap.congr_fun hh a
  have h2 : ev ((h a : W) : P × L).1 = φ (((h a : W) : P × L).2 : V) := (h a).2
  rw [h1] at h2
  exact h2

private theorem pv_add_siegel_theta_transformation {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (u v : Fin r → E) :
    pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  have hemb : ∀ τ : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (u + v) =
      ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u + ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := fun τ => by
    funext a
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  funext j
  simp only [pv, Function.comp_apply, Pi.add_apply, GlobalTheory.ThFr.per, hemb]
  split_ifs
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · rw [Matrix.mulVec_add, Pi.add_apply]

theorem exists_mark : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk ∧ A.Marked mk := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  have := Dw.proj
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom ℂ y.x _ y.x_over

  obtain ⟨m, hm, c0, hc0, hmc⟩ : ∃ m ∈ l.Mb, ∃ c0 ∈ Mfr l, m + c0 = 1 := by
    have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hMC : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hex0 : A.ex 0 = 1 := mul_left_cancel (a := A.ex 0) (by rw [_root_.mul_one, ← A.ex_add, add_zero])
  have hexn : ∀ (n : ℕ) z, A.ex (n • z) = A.ex z ^ n := by
    intro n z
    induction n with
    | zero => rw [zero_smul, hex0, pow_zero]
    | succ n ih => rw [succ_nsmul, A.ex_add, ih, pow_succ]
  have hpvs : ∀ (a : E) (v : Fin r → E), pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
    fun a v => pv_smul idx x a v
  have hinj : Function.Injective (pv X idx x) := (hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.2.1
  have hsv : ∀ (s : 𝓞 E) (v : Fin r → E), s • v = (s : E) • v := fun _ _ => rfl

  let φ : (Fin r → E) → (ptO Xo y.x ⟶ Xo.univ.t.G) := fun v => A.ex (pv X idx x ((l.M : E)⁻¹ • v))
  have hφadd : ∀ u v, φ (u + v) = φ u * φ v := fun u v => by
    simp only [φ, smul_add, pv_add_siegel_theta_transformation, A.ex_add]
  have hφlin : ∀ (s : 𝓞 E) v, φ (s • v) = φ v ≫ Xo.univ.t.act.act s := fun s v => by
    simp only [φ]
    rw [← A.ex_lin, ← hpvs, hsv, smul_comm]

  have heta : ∀ a, Xo.univ.eta a = Xo.univ.eta (c0 • a) := by
    intro a
    have h1 : a = c0 • a + m • a := by rw [← add_smul, add_comm, hmc, one_smul]
    conv_lhs => rw [h1]
    rw [Xo.univ.eta_add, Xo.univ.eta_ker (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top),
      _root_.mul_one]
  have hlev : ∀ a, levPt Xo y.x a = I.ev l.M (c0 • a) := by
    intro a
    rw [levPt, heta a]
    exact hI _ (Submodule.smul_mem_smul hc0 Submodule.mem_top)
  obtain ⟨mk, hmk⟩ := exists_lift_of_projective (fun s q => q ≫ Xo.univ.t.act.act s) L
    (fun a => I.ev l.M (c0 • a)) φ (fun a b => by rw [smul_add, I.add])
    (fun s a => by rw [smul_comm c0 s a, I.lin]) hφadd hφlin (by
      intro a
      obtain ⟨z, hz⟩ := A.ex_onto (I.ev l.M (c0 • a))
      have hp : A.ex z ^ l.M = 1 := by
        rw [hz]
        exact (I.onto l.M hM0 _).mpr ⟨_, rfl⟩
      rw [← hexn] at hp
      obtain ⟨v, hv, hzv⟩ := (A.ex_ker _).mp hp
      refine ⟨v, hv, ?_⟩
      rw [← hz]
      show A.ex z = A.ex (pv X idx x ((l.M : E)⁻¹ • v))
      congr 1
      rw [hpvs, ← hzv]
      funext j
      simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
      rw [inv_mul_cancel_left₀ hMC])

  have hevmk : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), I.ev l.M a = φ (mk a) := by
    intro a ha
    rw [← hI a ha, ← (hmk a).2]
    exact hlev a

  have hdiff : ∀ u v, φ u = φ v → ∃ w ∈ L, u - v = l.M • w := by
    intro u v huv
    have h1 : φ (u - v) = 1 := by
      have h2 := hφadd (u - v) v
      rw [sub_add_cancel, huv] at h2
      exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
    obtain ⟨w, hw, hw'⟩ := (A.ex_ker _).mp h1
    refine ⟨w, hw, ?_⟩
    have h3 := hinj hw'
    rw [← h3, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hME]

  have hML : ∀ v ∈ Mfr l • L, ∃ u ∈ L, m • v = l.M • u := by
    intro v hv
    have h1 : m • v ∈ (l.Mb * Mfr l) • L := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hm hv
    rw [Mfr, l.prod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨u, hu, by rw [← hu', Nat.cast_smul_eq_nsmul]⟩
  refine ⟨mk, ⟨fun a => (hmk a).1, ?_, ?_⟩, fun a _ => (hlev a).trans (hmk a).2⟩
  · intro a ha hau
    obtain ⟨u, hu, hau⟩ := hau
    apply (I.ker l.M hM0 a).mp
    rw [hevmk a ha]
    show A.ex (pv X idx x ((l.M : E)⁻¹ • mk a)) = 1
    rw [hau, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hME]
    exact (A.ex_ker _).mpr ⟨u, hu, rfl⟩
  · intro v hv
    have hvL : v ∈ L := Submodule.smul_le_right hv
    have hp : φ v ^ l.M = 1 := by
      have h1 : l.M • pv X idx x ((l.M : E)⁻¹ • v) = pv X idx x v := by
        rw [hpvs]
        funext j
        simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
        rw [mul_inv_cancel_left₀ hMC]
      show A.ex (pv X idx x ((l.M : E)⁻¹ • v)) ^ l.M = 1
      rw [← hexn, h1]
      exact (A.ex_ker _).mpr ⟨v, hvL, rfl⟩
    obtain ⟨a0, ha0⟩ := (I.onto l.M hM0 (φ v)).mp hp
    have haM : c0 • a0 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hc0 Submodule.mem_top
    have h3 : φ (mk (c0 • a0)) = φ (c0 • v) := by
      rw [← hevmk _ haM, I.lin, ha0, hφlin]
    obtain ⟨w, hw, hw'⟩ := hdiff _ _ h3.symm
    obtain ⟨u', hu', hmv⟩ := hML v hv
    refine ⟨c0 • a0, haM, u' + w, L.add_mem hu' hw, ?_⟩
    calc v = m • v + c0 • v := by rw [← add_smul, hmc, one_smul]
      _ = mk (c0 • a0) + (l.M • u' + l.M • w) := by rw [hmv, ← hw']; abel
      _ = mk (c0 • a0) + l.M • (u' + w) := by rw [smul_add]

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumnsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_symplectic_unitary_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  first | exact @GlobalTheory.ColumnSymplectic.exists_symplectic_columns | exact GlobalTheory.ColumnSymplectic.exists_symplectic_columns | (intros; apply GlobalTheory.ColumnSymplectic.exists_symplectic_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MaximalIsotropicDoubledGraphOrIsotropicStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  first | exact @GlobalTheory.SW.lag_graph_or_isotropic | exact GlobalTheory.SW.lag_graph_or_isotropic | (intros; apply GlobalTheory.SW.lag_graph_or_isotropic <;> assumption)
end

