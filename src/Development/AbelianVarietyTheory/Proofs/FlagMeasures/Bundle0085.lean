import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0083
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClasses
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP
  have hK : S.K0 ≤ S.St := inf_le_left.trans inf_le_left
  have key := mass_orbits_eq_tsum_fiber S.St S.K0 (fun Λ => S.IsTerm d Λ ∧ P Λ) (S.Fr d) hK
    (by
      rintro h hh Λ ⟨ht, hp⟩
      obtain ⟨ht', -, -, -, hFr, -⟩ := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ ht h hh
      have hlat := (TermBasic.term_basic L r k S d Λ ht).1.1
      exact ⟨⟨ht', hP h hh Λ ht hp⟩, hFr, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hlat).2.2 h hh⟩)
    (by
      rintro Λ ⟨ht, -⟩
      have tb := TermBasic.term_basic L r k S d Λ ht
      have hA := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ tb.1.1
      have hC := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 (S.Fr d Λ) tb.2.2.2.2.2.2.1.1
      exact ⟨hA.1, hA.2.1, hC.1, hC.2.1⟩)
  beta_reduce at key
  unfold Frames.mass Frames.mu
  refine Eq.trans ?_ (key.trans ?_)
  · exact tsum_congr fun o => by split_ifs <;> rfl
  unfold Frames.sumCls Frames.nT Frames.wC
  refine tsum_congr fun c => ?_
  by_cases hc : S.IsIntCls c.out
  · rw [if_pos hc]
    have hs : {x | (S.IsTerm d x ∧ P x) ∧ S.Fr d x = c.out}
        = {Λ | S.IsTerm d Λ ∧ P Λ ∧ S.Fr d Λ = c.out} := by
      ext Λ
      simp only [Set.mem_ofPred_eq, and_assoc]
    rw [hs]
  · rw [if_neg hc]
    have hs : {x | (S.IsTerm d x ∧ P x) ∧ S.Fr d x = c.out} = (∅ : Set (Submodule L.O S.V)) := by
      ext Λ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ht, -⟩, hF⟩
      exact hc (hF ▸ (TermBasic.term_basic L r k S d Λ ht).2.2.2.2.2.2.1)
    rw [hs, Set.encard_empty]
    simp

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfStabilizerSmulEqConj
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem inf_stabilizer_smul_eq_conj {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem hh h1) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_conj_of_invVol_conj {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by
  have e : ∀ A B : Subgroup G,
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have hpos : 0 < invVol K (MulAut.conj g • A) := by
    rw [h]; exact (invVol_mul_pos_le_conj K A A hA hA' hA hA').2.1
  have hAB : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hA' hB
  have hBA : B.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hB' hA
  have c1 : K.relIndex (MulAut.conj g • A) ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c2 : (MulAut.conj g • A).relIndex K ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c3 : K.relIndex (MulAut.conj g • B) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans c1 (by rw [e]; exact hAB)
  have c4 : (MulAut.conj g • B).relIndex K ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (by rw [e]; exact hBA) c2
  rw [(invVol_mul_pos_le_conj K _ _ c1 c2 c3 c4).1, (invVol_mul_pos_le_conj K A B hA hA' hB hB').1, h]
  congr 1
  rw [invVol, invVol, e, e]

theorem Frames.nu_pos_and_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 < S.nu d ∧ ∀ h ∈ S.H0, S.nu (h • d) = S.nu d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hv, hd⟩ := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement L r k S
  obtain ⟨d1, d2⟩ := hd d Λ hT
  have hSD := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  obtain ⟨l1, l2, l3⟩ := hv Λ hSD.1
  refine ⟨(invVol_mul_pos_le_conj _ _ _ d1 d2 d1 d2).2.1, fun h hh => ?_⟩
  have := l3 h hh
  rw [inf_stabilizer_smul_eq_conj _ hh] at this
  unfold Frames.nu
  rw [inf_stabilizer_smul_eq_conj _ hh]
  exact invVol_conj_of_invVol_conj _ _ _ h l1 l2 d1 d2 this

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatInIsLattice
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimCount

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpan.exists_smul_mem
  | exact _root_.GlobalTheory.SmulMemSpan.exists_smul_mem
  | (apply _root_.GlobalTheory.SmulMemSpan.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpan.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpan.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpan.exists_smul_mem ..)

theorem latIn_isLattice (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (latIn U L) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro u _
    obtain ⟨r, hr, hu⟩ := exists_smul_mem L hL (u : V)
    have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    have h2 : r • u ∈ Submodule.span K (latIn U L : Set U) := Submodule.subset_span hu
    rw [← algebraMap_smul K r] at h2
    exact (Submodule.smul_mem_iff _ h1).1 h2

end

theorem one_le_rd (K : Type) [Field K] [NumberField K] : 1 ≤ 2 * vInv K := by
  have h : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero K)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * fDeg K)) (by positivity)
  unfold vInv
  linarith

theorem real_bound (a : ℝ) (ha : 1 ≤ a) (n k f : ℕ) (hn : 1 ≤ n) (hf : 0 < f) :
    (1 + 2 * Real.sqrt (a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)))) ^ (2 * k * f) ≤
      (9 * a) ^ (k * f) * (n : ℝ) ^ ((k : ℝ) / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have h1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * f)) := Real.one_le_rpow hn' (by positivity)
  have e : (n : ℝ) ^ ((k : ℝ) / 2) = ((n : ℝ) ^ ((1 : ℝ) / (2 * f))) ^ (k * f) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [e, ← mul_pow, mul_assoc 2, pow_mul]
  set B := a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le ha h1
  have hs : 1 ≤ Real.sqrt B := Real.one_le_sqrt.2 hB1
  have hq : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [mul_assoc, ← hB]
  nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ n : ℕ, 1 ≤ n → (((primSp h L 1 n).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((9 * (2 * vInv K)) ^ (Module.finrank K V * fDeg K) * (n : ℝ) ^ ((Module.finrank K V : ℝ) / 2)) ∧ (primSp h L 0 n).encard ≤ 1 := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL n hn
  constructor
  · set B : ℝ := (2 * vInv K) * (n : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) with hB
    have hrd := one_le_rd K
    have hB0 : 0 ≤ B := by positivity
    have hsub : primSp h L 1 n ⊆ (fun x : V => Submodule.span K {x}) ''
        {x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
      rintro U ⟨hU, hd⟩
      obtain ⟨x, hx, hx0, hxB⟩ := GlobalTheory.T.exists_short_vector_integralHermitianLattice_rank_one K U (hRes h U) hK ⟨fun x y => hs.eq x y⟩
        (fun τ x hx => hp τ x (by simpa using hx)) hU (latIn U L)
        ⟨latIn_isLattice L hL.1 U, fun x hx y hy => hL.2 x hx y hy⟩
      rw [hd] at hxB
      refine ⟨x, ⟨hx, hxB⟩, ?_⟩
      refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 x.2) ?_
      rw [hU, finrank_span_singleton (by simpa using hx0)]
    have h1 := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
    refine le_trans (by exact_mod_cast h1) ((GlobalTheory.T.encard_shortVectors_le' K V h hK hs hp L hL B hB0).trans ?_)
    exact ENNReal.ofReal_le_ofReal (real_bound _ hrd n _ _ hn Fintype.card_pos)
  · rw [Set.encard_le_one_iff]
    rintro U W ⟨hU, -⟩ ⟨hW, -⟩
    rw [Submodule.finrank_eq_zero.1 hU, Submodule.finrank_eq_zero.1 hW]

end GlobalTheory.Mass.PrimCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassEqConstMulContent
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.QuotMass

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem unif_pow_mem (L : LocE F E) (ϖ : 𝒪[F]) (e : ℕ) : algebraMap F E ((ϖ : F) ^ e) ∈ L.O :=
  (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem ϖ.2 e)

theorem exists_pow_mul (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (c : E) :
    ∃ e : ℕ, algebraMap F E ((ϖ : F) ^ e) * c ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] c :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨e, (L.O_def _).2 ?_⟩
  have h1 := hd.smul (↑u⁻¹ : 𝒪[F])
  rw [smul_smul, hu, Units.inv_mul_cancel_left, Algebra.smul_def] at h1
  exact h1

theorem pow_smul_mono (L : LocE F E) (ϖ : 𝒪[F]) {n : ℕ} (Λ : Submodule L.O (Fin n → E))
    {v : Fin n → E} {e e' : ℕ} (h : e ≤ e') (hv : algebraMap F E ((ϖ : F) ^ e) • v ∈ Λ) :
    algebraMap F E ((ϖ : F) ^ e') • v ∈ Λ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, map_mul, mul_smul]
  exact Λ.smul_mem (⟨_, unif_pow_mem L ϖ k⟩ : L.O) hv

theorem exists_pow_smul (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {m : ℕ} (x : Fin m → Fin n → E) :
    ∃ e : ℕ, ∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ := by
  have h1 : ∀ v : Fin n → E, ∃ e : ℕ, algebraMap F E ((ϖ : F) ^ e) • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv => exact ⟨0, by simpa using hv⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨e, he⟩ := ha
      obtain ⟨f, hf⟩ := hb
      refine ⟨max e f, ?_⟩
      rw [smul_add]
      exact Λ.add_mem (pow_smul_mono L ϖ Λ (le_max_left _ _) he)
        (pow_smul_mono L ϖ Λ (le_max_right _ _) hf)
    | smul c a _ ha =>
      obtain ⟨e, he⟩ := ha
      obtain ⟨f, hf⟩ := exists_pow_mul L ϖ hϖ c
      refine ⟨f + e, ?_⟩
      have : algebraMap F E ((ϖ : F) ^ (f + e)) • c • a =
          (algebraMap F E ((ϖ : F) ^ f) * c) • algebraMap F E ((ϖ : F) ^ e) • a := by
        rw [smul_smul, smul_smul, pow_add, map_mul]; congr 1; ring
      rw [this]
      exact Λ.smul_mem (⟨_, hf⟩ : L.O) he
  choose e he using h1
  exact ⟨Finset.univ.sup fun a => e (x a), fun a =>
    pow_smul_mono L ϖ Λ (Finset.le_sup (f := fun a => e (x a)) (Finset.mem_univ a)) (he _)⟩

variable [CharZero F]

theorem cont_inf (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm) {Λs : Submodule L.O (Fin n → E)}
    (hs : IsSD L Hm Λs) {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hΛ' : IsLat L Λ') :
    ∃ i0 : ℕ, ∀ i ≥ i0, cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) x) i) *
      ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ (stabL L Λ ⊓ stabL L Λ')).relIndex
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) : ℝ) =
      ((isomG L Hm ⊓ stabL L Λ').relIndex (isomG L Hm ⊓ stabL L Λ) : ℝ) *
        cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ (stabL L Λ ⊓ stabL L Λ')) x) i) := by
  obtain ⟨N, hN⟩ := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ hΛ.1 1).2.2 Λ' hΛ'
  have hN' := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ' hΛ' 1).2.1 le_rfl
  obtain ⟨C, hC, hCi, hCn⟩ := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ hΛ.1 (max N 1)).1
  have hC1 := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ hΛ.1 (max N 1)).2.1 (le_max_right _ _)
  obtain ⟨e, he⟩ := exists_pow_smul L ϖ hϖ hΛ.1 x
  obtain ⟨i0, hi0, hth⟩ := GlobalTheory.T.thick_orbit_selfDual_unramified_lattice L ϖ hϖ Hm hH Λs hs Λ hΛ m _ hx (max N 1) e
  refine ⟨i0, fun i hi => ?_⟩
  set U := isomG L Hm with hU
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have hHU : H ≤ U := inf_le_left
  have hCS : C ≤ stabL L Λ := fun g hg => ((hC g).1 hg).1
  have hCS' : C ≤ stabL L Λ' := by
    intro g hg
    refine hN' g (hN g fun v hv => ?_)
    obtain ⟨w, hw, hgw⟩ := ((hC g).1 hg).2 v hv
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left N 1)
    refine ⟨algebraMap F E ((ϖ : F) ^ k) • w, Λ.smul_mem (⟨_, unif_pow_mem L ϖ k⟩ : L.O) hw, ?_⟩
    rw [hgw, hk, pow_add, map_mul, mul_smul]
  have h12 : U ⊓ C ≤ U ⊓ (stabL L Λ ⊓ stabL L Λ') := inf_le_inf_left _ (le_inf hCS hCS')
  have h1 : U ⊓ (stabL L Λ ⊓ stabL L Λ') ≤ U ⊓ stabL L Λ := inf_le_inf_left _ inf_le_left
  have hnorm : ∀ a ∈ U ⊓ stabL L Λ, MulAut.conj a • (U ⊓ C) = U ⊓ C := by
    intro a ha
    rw [Subgroup.smul_inf, hCn a ha.2, Subgroup.conj_smul_eq_self_of_mem ha.1]
  have hfin : ∀ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), ∀ T, T ≤ stabL L Λ →
      (K ⊓ C).relIndex (K ⊓ T) ≠ 0 := by
    intro K T hT
    have h := Subgroup.relIndex_ne_zero_trans (H := C) (K := stabL L Λ) (L := K ⊓ T)
    have h2 : C.relIndex (K ⊓ T) ≠ 0 := fun h0 =>
      hCi (Subgroup.relIndex_eq_zero_of_le_right (inf_le_right.trans hT) h0)
    rwa [← Subgroup.inf_relIndex_right (K ⊓ C), show K ⊓ C ⊓ (K ⊓ T) = C ⊓ (K ⊓ T) by
      ext g; simp only [Subgroup.mem_inf]; tauto, Subgroup.inf_relIndex_right]
  obtain ⟨hco, hst⟩ := hth i hi (U ⊓ C) (h12.trans h1)
    (fun g hg hg' => ⟨hg, (hC g).2 ⟨hC1 g hg', hg'⟩⟩) x he rfl
  have e1 := GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup L ϖ hϖ Hm hH Λs hs m x hx (U ⊓ stabL L Λ) (U ⊓ C) inf_le_left
    (h12.trans h1) hnorm (hfin U _ le_rfl) i (hi0.trans hi) hst hco
  have e2 := GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup L ϖ hϖ Hm hH Λs hs m x hx (U ⊓ (stabL L Λ ⊓ stabL L Λ')) (U ⊓ C)
    inf_le_left h12 (fun a ha => hnorm a (h1 ha)) (hfin U _ inf_le_left) i (hi0.trans hi) hst hco
  have hHi : ∀ T, H ⊓ (U ⊓ T) = H ⊓ T := fun T => by rw [← inf_assoc, inf_eq_left.2 hHU]
  rw [← hHdef] at e1 e2
  simp only [hHi] at e1 e2
  have m1 := Subgroup.relIndex_mul_relIndex _ _ _ h12 h1
  have m2 := Subgroup.relIndex_mul_relIndex (H ⊓ C) (H ⊓ (stabL L Λ ⊓ stabL L Λ')) (H ⊓ stabL L Λ)
    (inf_le_inf_left _ (le_inf hCS hCS')) (inf_le_inf_left _ inf_le_left)
  have m3 : (U ⊓ (stabL L Λ ⊓ stabL L Λ')).relIndex (U ⊓ stabL L Λ) =
      (U ⊓ stabL L Λ').relIndex (U ⊓ stabL L Λ) := by
    rw [← Subgroup.inf_relIndex_right (U ⊓ stabL L Λ')]
    congr 1
    ext g; simp only [Subgroup.mem_inf]; tauto
  rw [← m1, ← m2, m3] at e1
  push_cast at e1
  have hne : ((H ⊓ C).relIndex (H ⊓ (stabL L Λ ⊓ stabL L Λ')) : ℝ) ≠ 0 := by
    exact_mod_cast hfin H _ inf_le_left
  apply mul_left_cancel₀ hne
  linear_combination e1 - ((U ⊓ stabL L Λ').relIndex (U ⊓ stabL L Λ) : ℝ) * e2

theorem relIndex_symm (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm)
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hΛ' : IsSD L Hm Λ') :
    ((isomG L Hm ⊓ stabL L Λ').relIndex (isomG L Hm ⊓ stabL L Λ) : ℝ) =
      (isomG L Hm ⊓ stabL L Λ).relIndex (isomG L Hm ⊓ stabL L Λ') := by
  obtain ⟨g, hg, hgΛ⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).2 Λ Λ' hΛ hΛ'
  have hfix : fixG L Hm (Submodule.span E (Set.range (Fin.elim0 : Fin 0 → Fin n → E))) =
      isomG L Hm := by
    rw [Set.range_eq_empty, Submodule.span_empty]
    refine inf_eq_left.2 fun a _ => ⟨fun v => by simp, fun v hv => ?_⟩
    rw [(Submodule.mem_bot E).1 hv]; simp
  have h := GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular L Hm hH 0 Fin.elim0 (by simp) Λ Λ hΛ.1 hΛ.1 g (by rwa [hfix])
  rw [hfix, hgΛ] at h
  have hne : ((isomG L Hm ⊓ stabL L Λ).relIndex (isomG L Hm ⊓ stabL L Λ') : ℝ) ≠ 0 := by
    exact_mod_cast (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ' Λ hΛ'.1 hΛ.1 (isomG L Hm)).1
  simp only [invVol, Subgroup.relIndex_self, Nat.cast_one, div_one] at h
  exact (div_eq_one_iff_eq hne).1 h

end

theorem mass_eq_const_mul_content : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ Λ, IsSD L Hm Λ → ∃ i0 : ℕ, ∀ i ≥ i0, invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) = κ * cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) x) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hs m x hx Λ0 h0
  have hΓ : IsHerm L (gramT L Hm x) := by
    funext a b
    exact DualInter.cj_hf hH _ _
  obtain ⟨e, he⟩ := exists_pow_smul L ϖ hϖ hs.1 x
  obtain ⟨j, hj, hth⟩ := GlobalTheory.T.thick_orbit_selfDual_unramified_lattice L ϖ hϖ Hm hH Λs hs Λs hs m _ hx 1 e
  have hth' := fun i hi => hth i hi (isomG L Hm ⊓ stabL L Λs) le_rfl
    (fun g hg hg' => ⟨hg, (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λs hs.1 1).2.1 le_rfl g hg'⟩) x he rfl
  have h1K := fun i hi => GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  have hcpos : 0 < cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) x) j) :=
    (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ _).2.2.2 (hth' j le_rfl).1
      ⟨_, _, ⟨1, Subgroup.one_mem _, rfl⟩, 1, (h1K j hj).1, rfl⟩
  have hhpos := ((h1K j hj).2.2 _ hΓ hx).2
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have hcomm : ∀ A B, IsLat L A → IsLat L B → (H ⊓ stabL L B).relIndex (H ⊓ stabL L A) ≠ 0 :=
    fun A B hA hB => (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L A B hA hB H).1
  have hvpos : 0 < invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) :=
    (GlobalTheory.HL.invVol_mul_pos_le_conj _ (H ⊓ stabL L Λs) _ (hcomm _ _ hs.1 h0) (hcomm _ _ h0 hs.1)
      (hcomm _ _ hs.1 h0) (hcomm _ _ h0 hs.1)).2.1
  refine ⟨invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) j) /
    cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) x) j), by positivity, ?_⟩
  intro Λ hΛ
  obtain ⟨i1, k1⟩ := cont_inf L ϖ hϖ hH hs x hx hΛ hs.1
  obtain ⟨i2, k2⟩ := cont_inf L ϖ hϖ hH hs x hx hs hΛ.1
  refine ⟨max j (max i1 i2), fun i hi => ?_⟩
  have hij : j ≤ i := (le_max_left _ _).trans hi
  have k1 := k1 i ((le_max_left _ _).trans ((le_max_right _ _).trans hi))
  have k2 := k2 i ((le_max_right _ _).trans ((le_max_right _ _).trans hi))
  rw [← hHdef] at k1 k2
  rw [inf_comm (stabL L Λs) (stabL L Λ), ← relIndex_symm L hH hΛ hs] at k2
  have lev := GlobalTheory.T.normalisedContent_thickenedSet_independent_of_level L ϖ hϖ Hm hH Λs hs m _ hΓ hx (torb (isomG L Hm ⊓ stabL L Λs) x)
    (by
      rintro _ ⟨g, hg, rfl⟩
      ext a b
      exact hg.1 _ _) j i hj hij (hth' j le_rfl).2 (hth' i hij).1
  have hsplit : H ⊓ (stabL L Λ ⊓ stabL L Λs) = (H ⊓ stabL L Λ) ⊓ (H ⊓ stabL L Λs) := inf_inf_distrib_left _ _ _
  have a1 : (H ⊓ (stabL L Λ ⊓ stabL L Λs)).relIndex (H ⊓ stabL L Λ0) ≠ 0 := by
    rw [hsplit]
    exact Subgroup.relIndex_inf_ne_zero (hcomm _ _ h0 hΛ.1) (hcomm _ _ h0 hs.1)
  have a2 : (H ⊓ stabL L Λ0).relIndex (H ⊓ (stabL L Λ ⊓ stabL L Λs)) ≠ 0 := fun h =>
    hcomm _ _ hΛ.1 h0 (Subgroup.relIndex_eq_zero_of_le_right (inf_le_inf_left _ inf_le_left) h)
  have v1 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ (H ⊓ stabL L Λ) _ (hcomm _ _ hΛ.1 h0) (hcomm _ _ h0 hΛ.1)
      a2 a1).2.2.1 (inf_le_inf_left _ inf_le_left)
  have v2 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ (H ⊓ stabL L Λs) _ (hcomm _ _ hs.1 h0) (hcomm _ _ h0 hs.1)
      a2 a1).2.2.1 (inf_le_inf_left _ inf_le_right)
  have hne : ((H ⊓ (stabL L Λ ⊓ stabL L Λs)).relIndex (H ⊓ stabL L Λ) : ℝ) ≠ 0 := by
    rw [hsplit, inf_comm, Subgroup.inf_relIndex_right]
    exact_mod_cast hcomm _ _ hΛ.1 hs.1
  rw [div_mul_eq_mul_div, eq_div_iff hcpos.ne']
  apply mul_left_cancel₀ hne
  rw [v1] at v2
  rw [← k1] at k2
  linear_combination
    (cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) *
      cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) x) j)) * v2 +
    (invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) *
      ((H ⊓ (stabL L Λ ⊓ stabL L Λs)).relIndex (H ⊓ stabL L Λs) : ℝ)) * lev +
    (invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) j)) * k2

end GlobalTheory.HL.QuotMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveHermitianSublatticeDiscriminantGeneratoStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  first | exact @GlobalTheory.Mass.PrimDisc.main | exact GlobalTheory.Mass.PrimDisc.main | (intros; apply GlobalTheory.Mass.PrimDisc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStabStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_St_approximating_local_elements : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  first | exact @GlobalTheory.HL.StrongSt.strong_approx_stab | exact GlobalTheory.HL.StrongSt.strong_approx_stab | (intros; apply GlobalTheory.HL.StrongSt.strong_approx_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotentStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unipotent_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  first | exact @GlobalTheory.HL.SAN.strong_approximation_unipotent | exact GlobalTheory.HL.SAN.strong_approximation_unipotent | (intros; apply GlobalTheory.HL.SAN.strong_approximation_unipotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumOverDataTermCountEqLatticeMassStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (C : Set S.FrP) (P : S.Datum → Submodule L.O S.V → Prop), (∀ h ∈ S.H0, ∀ d Λ, S.IsTerm d Λ → P d Λ → P (h • d) (h • Λ)) → (S.sumData fun d => S.nT d C (P d)) = ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V), if ∃ d, S.IsTerm d o.out ∧ P d o.out ∧ S.Fr d o.out = C then ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0 := by
  first | exact @GlobalTheory.HL.sumData_nT_eq_mass | exact GlobalTheory.HL.sumData_nT_eq_mass | (intros; apply GlobalTheory.HL.sumData_nT_eq_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComplement_moves_local_terms_with_data : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  first | exact @GlobalTheory.HL.LocalMove.main | exact GlobalTheory.HL.LocalMove.main | (intros; apply GlobalTheory.HL.LocalMove.main <;> assumption)
end

