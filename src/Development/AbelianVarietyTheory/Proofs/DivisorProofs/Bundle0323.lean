import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinForm
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitWeil.FourierPi (box isCompact_box exists_box_subset)
open scoped Topology

noncomputable section

namespace GlobalTheory.KSp

theorem mem_box_of_forall_dot {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {d : Type} [Fintype d] [DecidableEq d] (ψ : AddChar F ℂ) {t₀ : Fˣ}
    (ht : ψ t₀ ≠ 1) (s : Fˣ) {v : d → F} (hv : ∀ u ∈ box d s, ψ (u ⬝ᵥ v) = 1) :
    v ∈ box d (t₀ * s⁻¹) := by
  intro i _
  by_contra h
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, not_le] at h
  have hw : v i ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at h
    exact absurd h (not_lt_of_ge zero_le')
  apply ht
  have hu : (Pi.single i ((t₀ : F) / v i) : d → F) ∈ box d s := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      have e : (t₀ : F) / v j = ((t₀ * s⁻¹ : Fˣ) : F) * s / v j := by
        push_cast
        field_simp
      have hpos : 0 < valuation F (v j) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hw
      rw [e, map_div₀, map_mul, div_le_iff₀ hpos, mul_comm (valuation F (s : F))]
      exact mul_le_mul' h.le le_rfl
    · simp [Pi.single_eq_of_ne hj, GlobalTheory.SplitWeil.cball]
  have h2 := hv _ hu
  rwa [single_dotProduct, div_mul_cancel₀ _ hw] at h2

theorem isPair_addChar_form : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  intro F _ _ _ _ _ V _ _ _ _ _ ψ hψ hn h1 β hs hnd
  haveI := GlobalTheory.WeilM.nonarch_field F
  haveI := IsModuleTopology.toContinuousAdd F V
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact h1 (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ)
  let T : Fˣ := Units.mk0 t ht0
  have hT : ψ (T : F) ≠ 1 := ht
  let b := Module.finBasis F V
  let e₁ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := b.equivFun
  let f₂ : V →ₗ[F] (Fin (Module.finrank F V) → F) := LinearMap.pi fun i => β (b i)
  have hf₂ : Function.Injective f₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd y
    intro x
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, show β (b i) y = 0 from congrFun hy i, smul_zero]
  have hbij : Function.Bijective f₂ :=
    ⟨hf₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hf₂⟩
  let e₂ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := LinearEquiv.ofBijective f₂ hbij
  have key : ∀ u y, β (e₁.symm u) y = u ⬝ᵥ e₂ y := by
    intro u y
    simp [e₁, e₂, f₂, Module.Basis.equivFun_symm_apply, map_sum, map_smul, dotProduct]
  have cont : ∀ g : V ≃ₗ[F] (Fin (Module.finrank F V) → F), Continuous g ∧ Continuous g.symm := fun g =>
    ⟨IsModuleTopology.continuous_of_linearMap g.toLinearMap,
      IsModuleTopology.continuous_of_linearMap g.symm.toLinearMap⟩
  have ann : ∀ (s : Fˣ) y, (∀ u ∈ box (Fin (Module.finrank F V)) s, ψ (β (e₁.symm u) y) = 1) →
      e₂ y ∈ box (Fin (Module.finrank F V)) (T * s⁻¹) := by
    intro s y h
    exact mem_box_of_forall_dot ψ hT s fun u hu => by rw [← key]; exact h u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    rw [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul]
  · intro x y
    rw [hs]
  · intro x y
    exact hn _
  · exact (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous
      (IsModuleTopology.continuous_bilinear_of_finite_left β)
  · intro U hU
    have hU' : e₂.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₂).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨r, hr⟩ := exists_box_subset hU'
    refine ⟨e₁.symm '' box (Fin (Module.finrank F V)) (T * r⁻¹), (isCompact_box _).image (cont e₁).2,
      fun y hy => ?_⟩
    have h2 := ann (T * r⁻¹) y fun u hu => hy _ ⟨u, hu, rfl⟩
    rw [show T * (T * r⁻¹)⁻¹ = r by rw [_root_.mul_inv_rev, inv_inv, mul_comm r, mul_inv_cancel_left]] at h2
    simpa using hr h2
  · intro U hU
    have hU' : e₁.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₁).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨s, hs'⟩ := exists_box_subset hU'
    exact ⟨e₂.symm '' box (Fin (Module.finrank F V)) (T * s⁻¹), (isCompact_box _).image (cont e₂).2,
      fun y hy => ⟨e₂ y, ann s y fun u hu => hy _ (hs' hu), by simp⟩⟩

end GlobalTheory.KSp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal

namespace GlobalTheory.LGrp.SatakeCompare

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem isSubquotient_smInd_congr {G V W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {H H' : Subgroup G} (h : H = H') (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H), σ ⟨g, hg⟩ = σ' ⟨g, h ▸ hg⟩) (π : Representation ℂ G V) :
    _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H σ) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H' σ') := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g g.2
  rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem blk_points (n : Type) (j : n) :
    _root_.GlobalTheory.SmGL.blk (_root_.GlobalTheory.SmGL.points n) j = j :=
  _root_.GlobalTheory.SmGL.blk_apply (_root_.GlobalTheory.SmGL.points n) j ()

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_Q_eq_parab_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).Q =
      _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  simp only [_root_.GlobalTheory.SmGL.mem_parab, blk_points]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_p_apply_eq_diag (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) (i : n) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).p q i : kˣ) : k) = (q : GL n k) i i := rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem leviProj_points_eq_leviTorus_borel_p (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q)
    (hq : (q : GL n k) ∈ _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n)) :
    _root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points n) ⟨q, hq⟩ =
      _root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q) := by
  funext a
  ext i j
  rw [_root_.GlobalTheory.SmGL.leviProj_apply]
  cases i; cases j
  simp [_root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points, borelGL_p_apply_eq_diag]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem modulus_leviEmb_eq_smGL_modulus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) (U : Subgroup (GL n k))
    (hU : U = _root_.GlobalTheory.SmGL.unipRad k e) (hc : IsClosed (U : Set (GL n k)))
    (g : _root_.GlobalTheory.SmGL.Levi k m) (x : Subgroup.normalizer (U : Set (GL n k)))
    (hx : (x : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g) :
    ((_root_.GlobalTheory.LGrp.modulus U hc x : NNReal) : ℝ) = _root_.GlobalTheory.SmGL.modulus k m g := by
  obtain ⟨x, hg⟩ := x
  simp only at hx
  subst hx
  subst hU
  letI : MeasurableSpace (_root_.GlobalTheory.SmGL.unipRad k e) := borel _
  haveI : BorelSpace (_root_.GlobalTheory.SmGL.unipRad k e) := ⟨rfl⟩
  haveI : LocallyCompactSpace (_root_.GlobalTheory.SmGL.unipRad k e) :=
    hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (_root_.GlobalTheory.SmGL.unipRad k e) := Measure.haar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    inferInstance
  have hK : MeasurableSet (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    K.isCompact.isClosed.measurableSet
  have h1 := _root_.GlobalTheory.LGrp.modulus_measure _ hc μ ⟨_, hg⟩ (K : Set _)
  have h2 := _root_.GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul k α n m e μ g _ hK
  have hset : (_root_.GlobalTheory.LGrp.conjAut (_root_.GlobalTheory.SmGL.unipRad k e) ⟨_, hg⟩) '' (K : Set _) =
      {u : _root_.GlobalTheory.SmGL.unipRad k e | ∃ s ∈ (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)),
        (u : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g * (s : GL n k) *
          (_root_.GlobalTheory.SmGL.leviEmb k e g)⁻¹} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, _root_.GlobalTheory.LGrp.conjAut_coe _ _ _⟩
    · rintro ⟨s, hs, hu⟩
      exact ⟨s, hs, Subtype.ext ((_root_.GlobalTheory.LGrp.conjAut_coe _ _ _).trans hu.symm)⟩
  rw [hset, h2] at h1
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 := (ENNReal.mul_left_inj hpos hfin).1 h1
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact ((ENNReal.ofReal_eq_ofReal_iff (_root_.GlobalTheory.SmGL.modulus_pos k g).le
    (NNReal.coe_nonneg _)).1 h3).symm

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_U_eq_unipRad_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).U = _root_.GlobalTheory.SmGL.unipRad k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  rw [_root_.GlobalTheory.LGrp.LeviDatum.mem_U,
    _root_.GlobalTheory.SmGL.mem_unipRad, ← borelGL_Q_eq_parab_points]
  constructor
  · rintro ⟨hQ, hp⟩
    refine ⟨hQ, fun a i j => ?_⟩
    have h := congrArg (fun u : kˣ => (u : k)) (congrFun hp a)
    simp only [borelGL_p_apply_eq_diag, Pi.one_apply, Units.val_one] at h
    cases i; cases j
    simpa using h
  · rintro ⟨hQ, hd⟩
    refine ⟨hQ, funext fun a => Units.ext ?_⟩
    rw [borelGL_p_apply_eq_diag]
    simpa using hd a () ()

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_s_eq_leviEmb_points_leviTorus (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (t : n → kˣ) :
    (_root_.GlobalTheory.LGrp.borelGL k n).s t =
      _root_.GlobalTheory.SmGL.leviEmb k (_root_.GlobalTheory.SmGL.points n) (_root_.GlobalTheory.SmGL.leviTorus k n t) := by
  ext i j
  change ((_root_.GlobalTheory.LGrp.diagHom k n t : GL n k) : Matrix n n k) i j = _
  rw [_root_.GlobalTheory.LGrp.diagHom_val]
  simp [_root_.GlobalTheory.SmGL.leviEmb, _root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points]
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).deltaHalf q : ℂˣ) : ℂ) =
      ((_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : n => Unit)
        (_root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q)) : ℂˣ) : ℂ) := by
  rw [_root_.GlobalTheory.LGrp.LeviDatum.deltaHalf_coe, _root_.GlobalTheory.SmGL.val_deltaHalf,
    _root_.GlobalTheory.LGrp.LeviDatum.delta_apply,
    modulus_leviEmb_eq_smGL_modulus k (_root_.GlobalTheory.SmGL.points n) _
      (borelGL_U_eq_unipRad_points k n) _ _ _ (borelGL_s_eq_leviEmb_points_leviTorus k n _)]

open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in

theorem _root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) :
    _root_.GlobalTheory.LGrp.IsSubquot π (_root_.GlobalTheory.LGrp.psGL k α) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π
        (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar k (α i)) := by
  change _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.LGrp.psGL k α) ↔ _
  unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd _root_.GlobalTheory.LGrp.LeviDatum.nIndQ
  unfold _root_.GlobalTheory.SmGL.prinSeries _root_.GlobalTheory.SmGL.indB _root_.GlobalTheory.SmGL.parInd
  refine isSubquotient_smInd_congr (borelGL_Q_eq_parab_points k n) _ _ (fun g hg => ?_) π
  refine LinearMap.ext fun z => ?_
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.LGrp.twist_apply,
    _root_.GlobalTheory.LGrp.charRep_apply, _root_.GlobalTheory.SmGL.twist_apply,
    _root_.GlobalTheory.SmGL.ofChar_apply]
  rw [leviProj_points_eq_leviTorus_borel_p k n ⟨g, hg⟩, borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus]
  simp [_root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.LGrp.unrTorus_apply,
    _root_.GlobalTheory.LGrp.unrChar_eq]

open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in

theorem _root_.GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n V : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (S : Multiset ℂˣ), _root_.GlobalTheory.LGrp.HasSatakeGL π S ↔
      ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ _root_.GlobalTheory.SmGL.HasSatake π α := by
  intro k _ _ _ _ n V _ _ _ _ _ π S
  unfold _root_.GlobalTheory.LGrp.HasSatakeGL _root_.GlobalTheory.LGrp.InUPSGL _root_.GlobalTheory.SmGL.HasSatake
    _root_.GlobalTheory.SmGL.IsSpherical _root_.GlobalTheory.LGrp.IsIrrSmooth
  rw [_root_.GlobalTheory.LGrp.isSpherical_iff]
  constructor
  · rintro ⟨⟨α, hα, ⟨-, hirr⟩, hsub⟩, hsph⟩
    exact ⟨α, hα, hirr, hsph, (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).1 hsub⟩
  · rintro ⟨α, hα, hirr, hsph, hsub⟩
    have hsub' := (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).2 hsub
    refine ⟨⟨α, hα, ⟨?_, hirr⟩, hsub'⟩, hsph⟩
    refine _root_.GlobalTheory.SmGL.IsSubquotient.isSmooth hsub' ?_
    unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd
    exact _root_.GlobalTheory.LGrp.LeviDatum.nInd_isSmooth _ _

end GlobalTheory.LGrp.SatakeCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R]

theorem free_ext {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G)
    (h : ∀ U x, Sec.map a (freeGen R P U x) = Sec.map b (freeGen R P U x)) : a = b := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down

theorem free_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let η : (freeP R).obj P ⟶ F.obj :=
    { app := fun U => ModuleCat.freeDesc (TypeCat.ofHom fun x => a U.unop x.down)
      naturality := fun U V g => by
        apply ModuleCat.free_hom_ext
        intro x
        change (ModuleCat.freeDesc _) ((ModuleCat.free _).map _ (ModuleCat.freeMk x)) =
          (F.obj.map g) ((ModuleCat.freeDesc _) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        exact (ha V.unop U.unop g.unop x.down).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm η,
    fun U x => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ F).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h) (ModuleCat.freeMk (ULift.up x))
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom (ModuleCat.free_map_apply _ _)

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))) (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.free_map_apply _ _)

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

def mapHom (F G : Shv R) {U : Scheme.{0}} (x : Sec F U) : (F ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun φ => Sec.map φ x) (fun _ _ => rfl)

theorem isZero_chains (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => ?_)
  change -(i : ℤ) = p at hi
  omega

theorem chains_d (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl
  have h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p
  rw [h1, Iso.inv_hom_id_assoc]
  exact congrArg (· ≫ (chainsXIso R E p).inv) h2

theorem chains_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ ((chainsN R).map f).f p ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

variable {E : Spc} {I : Cx R} {n : ℤ}

theorem ev_def (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl

theorem ev_ext (α β : Cochain ((chains R).obj E) I n) (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  ext p s hs : 1
  by_cases hp : p ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    exact free_ext _ _ (fun U x => h k s hs U x)
  · exact (isZero_chains E p (by omega)).eq_of_src _ _

theorem ev_exists (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x := by
  have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
      Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
        a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using key
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

theorem ev_res (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sx E p U) : Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  rw [ev_def, map_res, freeGen_res]
  rfl

theorem ev_add (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
  simp [ev, Cochain.add_v]

def evHom (I : Cx R) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun a => ev a p s h U x) (fun a b => ev_add a b p s h U x)

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := map_zero (evHom I n p s h U x)

theorem ev_zsmul (c : ℤ) (a : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • a) p s h U x = c • ev a p s h U x := map_zsmul (evHom I n p s h U x) c a

theorem ev_pull {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

theorem ev_δ_zero {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (s t : ℤ)
    (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
    ev (δ n m α) 0 t ht U x = Sec.map (I.d s t) (ev α 0 s hs U x) := by
  rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
    (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
  rfl

theorem ev_δ_succ {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
    Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
  refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
  rw [map_zsmul, map_sum, Units.smul_def]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [Preadditive.zsmul_comp, map_zsmul]
  congr 1
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

end GlobalTheory.EtC.CupSpec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationNormalizationRootAdjoinIsDVRStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_normalization_rootAdjoin_isDVR : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∃ _ : IsDomain (Localization.AtPrime Q), IsDiscreteValuationRing (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.LocNormDVR.main) | (exact GlobalTheory.LocNormDVR.main) | (intros; apply GlobalTheory.LocNormDVR.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusInversionAffineFinrankSubspacesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobiusInversion_affine_finrank_subspaces : ∀ (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ), 0 < Module.finrank K U → (∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 = c₀ + c * (Module.finrank K A : ℂ)) → G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.moebius_affine_finrank | exact GlobalTheory.CuspGL.moebius_affine_finrank | (intros; apply GlobalTheory.CuspGL.moebius_affine_finrank <;> assumption)
end

