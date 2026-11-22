import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0038
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermIntegralNearOneBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0083
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumClsLeEncard
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ClassCount

theorem tsum_le_encard {G X : Type*} [Group G] [MulAction G X] (H K0 : Subgroup G) (hK : K0 ≤ H)
    (P Q : X → Prop) (w : X → ℝ)
    (hP : ∀ x, P x → ∃ h ∈ H, w x = invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) ∧
      H ⊓ MulAction.stabilizer G (h • x) ≤ K0 ∧ ∀ k ∈ K0, Q (k • h • x)) :
    (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (w o.out) * 1 else 0)
      ≤ (({x | Q x} : Set X).encard : ℝ≥0∞) := by
  rw [encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X)) Q]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  swap
  · exact zero_le
  obtain ⟨h, hh, hw, hle, hQ⟩ := hP _ ho
  have h2 : (H ⊓ MulAction.stabilizer G (h • o.out)).relIndex K0
      = (MulAction.orbit K0 (h • o.out)).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hK hg, a⟩⟩
  have h3 : MulAction.orbit K0 (h • o.out) ⊆
      {x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ Q x} := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨?_, hQ g hg⟩
    conv_rhs => rw [← Quotient.out_eq' o]
    rw [Quotient.eq'', MulAction.orbitRel_apply]
    exact ⟨⟨g * h, mul_mem (hK hg) hh⟩, mul_smul g h o.out⟩
  rw [hw, invVol, Subgroup.relIndex_eq_one.2 hle, h2, Nat.cast_one, div_one, mul_one,
    ENNReal.ofReal_natCast]
  have h4 : ((MulAction.orbit K0 (h • o.out)).ncard : ℕ∞) ≤ _ :=
    (Set.ncard_le_encard _).trans (Set.encard_le_encard h3)
  exact_mod_cast h4

theorem sameBlock_trans {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∀ a b c : ℕ, sameBlock bs a b = true → sameBlock bs a c = true → sameBlock bs b c = true := by
  induction bs with
  | nil => intro a b c h; simp [sameBlock] at h
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    intro a b c h1 h2
    simp only [sameBlock, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact Or.inl ⟨h1.2, h2.2⟩
    · omega
    · omega
    · exact Or.inr ⟨⟨h1.2, h2.2⟩, ih _ _ _ h1' h2'⟩

theorem isUni_mul {E : Type} [CommRing E] {N : ℕ} {s u : Matrix (Fin N) (Fin N) E}
    (hs : IsUni s) (hu : IsUni u) : IsUni (s * u) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hs.1 i l h, zero_mul]
    · rw [hu.1 l j (hij.trans_le h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, hu.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hs.1 i l h, zero_mul]
      · rw [hu.1 l i h, mul_zero]
    · simp

theorem apply_frame {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {N : ℕ}
    (g : V ≃ₗ[E] V) (f : Fin N → V) (s u : Matrix (Fin N) (Fin N) E)
    (hs : ∀ j, g (f j) = ∑ i, s i j • f i) (j : Fin N) :
    g (∑ i, u i j • f i) = ∑ i, (s * u) i j • f i := by
  simp only [map_sum, map_smul, hs, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem smul_span (g : S.GLV) (f : Fin (r + 1) → S.V) :
    g • Submodule.span L.O (Set.range f) = Submodule.span L.O (Set.range fun b => g (f b)) := by
  rw [Submodule.smul_span, ← Set.image_smul, ← Set.range_comp]
  rfl

theorem isIntCls_smul {h : S.GLV} (hh : h ∈ S.St) {C : Set S.FrP} (hC : S.IsIntCls C) :
    S.IsIntCls (h • C) := by
  obtain ⟨⟨n, hn, n', hn', rfl⟩, hI⟩ := hC
  refine ⟨⟨h * n, mul_mem hh.1 hn, h * n', mul_mem hh.2 hn', ?_⟩, ?_⟩
  · rw [(GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 h]
    rfl
  · rintro _ ⟨p, hp, rfl⟩ a b
    have := hh.1.1.1 (p.2 b) (p.1 a)
    have h2 := hI p hp a b
    rw [Frames.h, ← this] at h2
    exact h2

theorem span_le_of_mem {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    Submodule.span L.O (Set.range p.1) ≤ Submodule.span L.O (Set.range g) := by
  obtain ⟨A, A', hA, -, -, -, -, h1, -⟩ := hp
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  rw [h1 j]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem _ (⟨A i j, hA i j⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)

theorem stab_le (g g' : Fin (r + 1) → S.V) :
    MulAction.stabilizer S.GLV (S.frameCls g g') ≤ stabL L (Submodule.span L.O (Set.range g)) := by
  intro h hh
  have h1 : h • S.frameCls g g' = S.frameCls g g' := hh
  rw [(GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 h] at h1
  change h • Submodule.span L.O (Set.range g) = _
  rw [smul_span]
  refine le_antisymm ?_ ?_
  · exact span_le_of_mem S (p := (_, _)) (h1 ▸ (GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).1)
  · exact span_le_of_mem S (p := (g, g')) (h1.symm ▸ (GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).1)

theorem matrix_of_mem {g : S.GLV} (hg : g ∈ S.K0) :
    ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s ∧ IsUni s' ∧ IsIntM L s ∧
      (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) ∧
      (∀ j, g (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, g (S.f' j) = ∑ i, s' i j • S.f' i := by
  obtain ⟨s, hs, e⟩ := (FrameOnto.unipotent_onto L r k S).1 g hg.1.1.1
  obtain ⟨s', hs', e'⟩ := (FrameOnto.unipotent_onto L r k S).2.1 g hg.1.1.2
  have hz := ((GlobalTheory.T.frames_commonStabiliser_eq_pairingMatrix_stabiliser L r k S).2 s s' hs hs').2 ⟨g, hg.1.1, e, e'⟩
  have hb := ((GlobalTheory.T.hermitianFrames_pairingStabilizer_blockDiagonal L r k S).1 s s' hs hs' hz).1
  refine ⟨s, s', hs, hs', fun i j => ?_, fun i j h => (hb i j h).1, e, e'⟩
  have h1 : g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := hg.1.2
  rw [smul_span] at h1
  have h2 : g (S.f j) ∈ Submodule.span L.O (Set.range S.f) :=
    h1 ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have li : LinearIndependent E S.f :=
    (GlobalTheory.FrameBasic.main L r k S).1.comp Sum.inl Sum.inl_injective
  have h3 := Fintype.linearIndependent_iff.1 li (fun i => s i j - c i) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← e j, ← hc]
    exact sub_self _) i
  rw [sub_eq_zero.1 h3]
  exact (c i).2

end

theorem sumCls_le_encard : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (S.sumCls fun _ => 1) ≤ ({C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i}.encard : ℝ≥0∞) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine tsum_le_encard S.St S.K0 (fun _ h => h.1.1) S.IsIntCls _ S.wC fun C hC => ?_
  have hC' := hC
  obtain ⟨⟨n, hn, n', hn', rfl⟩, -⟩ := hC'
  obtain ⟨h, hh, hle, u, hu, hub, e⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
  obtain ⟨u', hu', e'⟩ := (FrameOnto.unipotent_onto L r k S).2.1 (h⁻¹ * n')
    (S.N'.mul_mem (S.St.inv_mem hh).2 hn')
  refine ⟨h⁻¹, inv_mem hh, (((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ hC.1).2.2.2 _ (inv_mem hh)).symm, ?_, ?_⟩
  · rintro g ⟨g1, g2⟩
    have h1 : h * g * h⁻¹ ∈ MulAut.conj h • S.K0 := by
      refine hle ⟨S.St.mul_mem (S.St.mul_mem hh g1) (S.St.inv_mem hh), stab_le S _ (fun b => n' (S.f' b)) ?_⟩
      have g3 : g • h⁻¹ • _ = h⁻¹ • _ := g2
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, g3, smul_inv_smul]
    exact (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj h) (x := g)).1 h1
  · intro g hg
    obtain ⟨s, s', hs, hs', hi, hb, d, d'⟩ := matrix_of_mem S hg
    refine ⟨isIntCls_smul S hg.1.1 (isIntCls_smul S (S.St.inv_mem hh) hC), s * u, s' * u',
      isUni_mul hs hu, isUni_mul hs' hu', fun i j hij => ?_, ?_⟩
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun l _ => ?_
      cases hl : sameBlock S.w.blocks i l
      · rw [hb i l hl, zero_mul]; exact zero_mem _
      · exact mul_mem (hi i l) (hub l j (sameBlock_trans _ _ _ _ hl hij))
    · rw [(GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 h⁻¹, (GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 g]
      congr 1
      · funext j
        rw [e j, apply_frame g S.f s u d]
      · funext j
        rw [← apply_frame g S.f' s' u' d', ← e' j]
        rfl

end GlobalTheory.HL.ClassCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermIntegralNearOneBoundStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_integral_near_one_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → |(cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re * (S.q : ℝ) ^ S.a - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re * (S.q : ℝ) ^ S.a ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ∀ y : S.V, (∃ u ∈ S.refU J Λ, L.psi0 (S.h y u) ≠ 1) → ‖cint (S.refU J Λ) (fun u => ind (fun u => u ∈ S.refU J Λ ∧ S.InZ u) u * L.psi0 (S.h y u))‖ * (S.q : ℝ) ^ S.a ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.FibU.shares | exact GlobalTheory.HL.FibU.shares | (intros; apply GlobalTheory.HL.FibU.shares <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  first | exact @GlobalTheory.HL.CoordTermWt.terms_correspond | exact GlobalTheory.HL.CoordTermWt.terms_correspond | (intros; apply GlobalTheory.HL.CoordTermWt.terms_correspond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.InvH

theorem tsum_orbit_normaliser {G X M : Type} [Group G] [MulAction G X] [AddCommMonoid M]
    [TopologicalSpace M] (K : Subgroup G) (h : G) (h1 : ∀ s ∈ K, h * s * h⁻¹ ∈ K)
    (h2 : ∀ s ∈ K, h⁻¹ * s * h ∈ K) (φ ψ : X → M) (hφ : ∀ s ∈ K, ∀ x, φ (s • x) = φ x)
    (hψ : ∀ x, ψ (h • x) = φ x) :
    ∑' o : MulAction.orbitRel.Quotient K X, ψ o.out =
      ∑' o : MulAction.orbitRel.Quotient K X, φ o.out := by
  let e : MulAction.orbitRel.Quotient K X ≃ MulAction.orbitRel.Quotient K X :=
    Quotient.congr (MulAction.toPerm h) (by
      intro a b
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h1 s s.2⟩, ?_⟩
        rw [← hs]
        simp [Subgroup.smul_def, mul_smul]
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h2 s s.2⟩, ?_⟩
        simp only [Subgroup.smul_def, mul_smul] at hs ⊢
        rw [hs]; simp)
  rw [← e.tsum_eq]
  refine tsum_congr fun o => ?_
  have h3 : e o = Quotient.mk _ (h • o.out) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have h4 : (MulAction.orbitRel K X) (e o).out (h • o.out) := by
    rw [h3]; exact Quotient.mk_out (s := MulAction.orbitRel K X) _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : (e o).out = h • ((h⁻¹ * s * h) • o.out) := by
    rw [← hs]; simp [Subgroup.smul_def, mul_smul]
  rw [h5, hψ, hφ _ (h2 s s.2)]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} {h s : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (hs : s ∈ unipOn A B) :
    h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h.symm v ∈ A ↔ v ∈ A := fun v => by rw [← hA]; simp
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h.symm v)) ∈ A ↔ _
    rw [hA, hs.1, hA']
  · have := (hB _).2 (hs.2 _ ((hA' v).2 hv))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this

theorem mem_iff_of_fix {n : ℕ} {A : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v ∈ A, h v = v) (v : Fin n → E) : h v ∈ A ↔ v ∈ A := by
  constructor
  · intro hv
    have := h.injective (hA _ hv)
    rwa [this] at hv
  · intro hv; rwa [hA v hv]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (hij : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha hij)

theorem conj_Nof (g : Fin (r + 1) → S.V) {h s : S.GLV} (hi : h ∈ isomG L S.Hm)
    (hg : ∀ v ∈ S.spanTo g (r + 1), h v = v) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  have hfix : ∀ j ≤ r + 1, ∀ v, h v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := fun j hj =>
    mem_iff_of_fix fun v hv => hg v (spanTo_mono S g hj hv)
  obtain ⟨⟨s1, s2⟩, s3⟩ := hs
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hi s1) ((isomG L S.Hm).inv_mem hi), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun j => ?_
    exact conj_unipOn (hfix _ (by omega)) (hfix _ (by omega)) (Subgroup.mem_iInf.1 s2 j)
  · refine conj_unipOn (fun v => ?_) (hfix _ (by omega)) s3
    refine forall₂_congr fun y hy => ?_
    have := hi v y
    rw [hg y (spanTo_mono S g (by omega) hy)] at this
    rw [this]

theorem conj_St {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : h * s * h⁻¹ ∈ S.St := by
  have hfix : ∀ v ∈ S.ME, h v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 v hv))
  exact ⟨conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_left hv)) hs.1,
    conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_right hv)) hs.2⟩

theorem amp_mass_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, ∀ (d : S.Datum) (Q Q' : Submodule L.O S.V → Prop), (∀ s ∈ S.St, ∀ Λ, S.IsTerm d Λ → Q Λ → Q (s • Λ)) → (∀ Λ, S.IsTerm d Λ → (Q Λ ↔ Q' (h • Λ))) → S.amp (h • d) Q' = S.amp d Q ∧ S.mass (h • d) Q' = S.mass d Q := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh d Q Q' hQ hQ'
  have c1 : ∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St := fun s hs => conj_St S hh hs
  have c2 : ∀ s ∈ S.St, h⁻¹ * s * h ∈ S.St := fun s hs => by
    simpa using conj_St S (inv_mem hh) hs
  have aS := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d
  have aH := GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms L r k S
  have hmu : ∀ Λ, S.IsTerm d Λ → ∀ s ∈ S.St, S.mu (s • Λ) = S.mu Λ := fun Λ hΛ =>
    ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).1.1).2.2
  have iS : ∀ s ∈ S.St, ∀ Λ, (S.IsTerm d (s • Λ) ∧ Q (s • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro s hs Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aS _ a _ (inv_mem hs)).1
      have b' := hQ _ (inv_mem hs) _ a b
      rw [inv_smul_smul] at a' b'
      exact ⟨a', b'⟩
    · rintro ⟨a, b⟩
      exact ⟨(aS _ a _ hs).1, hQ _ hs _ a b⟩
  have iH : ∀ Λ, (S.IsTerm (h • d) (h • Λ) ∧ Q' (h • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aH _ _ a _ (inv_mem hh)).1
      rw [inv_smul_smul, inv_smul_smul] at a'
      exact ⟨a', (hQ' _ a').2 b⟩
    · rintro ⟨a, b⟩
      exact ⟨(aH _ _ a _ hh).1, (hQ' _ a).1 b⟩
  constructor
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then (S.mu Λ : ℂ) * S.om d Λ else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then (S.mu Λ : ℂ) * S.om (h • d) Λ else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs, (aS _ a.1 s hs).2.1])
        fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ)
        (fun a => by rw [(aH _ _ a.1 h hh).2.1, (aH _ _ a.1 h hh).2.2.1]) fun _ => rfl
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then ENNReal.ofReal (S.mu Λ) else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then ENNReal.ofReal (S.mu Λ) else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs]) fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ) (fun a => by rw [(aH _ _ a.1 h hh).2.2.1]) fun _ => rfl

end GlobalTheory.InvH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTerms
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplMove

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma bbne_img (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by
  have hfam : ∀ i, g (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i := by
    intro i
    unfold HermSp.MMfam
    rcases hs : M.split with _ | gg <;> rcases i with i | i <;>
      simp [map_smul, map_sub, (hfix i).1, (hfix i).2]
  have hspan : ∀ v ∈ Submodule.span E (Set.range (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r))), g v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfam i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul s x _ hx => rw [map_smul, hx]
  have e : H.MMfam (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) := rfl
  unfold LocNG.BBne
  simp only [e]
  constructor
  · rintro ⟨v, hv, hs, hns⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have ew : g w = w := g.injective (hspan _ hs)
    change g w ∈ _ at hs
    change g w ∉ _ at hns
    rw [ew] at hs hns
    exact ⟨w, hw, hs, hns⟩
  · rintro ⟨v, hv, hs, hns⟩
    exact ⟨v, Submodule.mem_map.2 ⟨v, hv, hspan v hs⟩, hs, hns⟩

lemma fwd (hM : M.OK) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : Coord P S) (g : V ≃ₗ[E] V)
    (hg : c.grp g ∈ S.H0) (d d' : LocNG.Datum P) (hmv : c.grp g • c.dat d = c.dat d')
    (f f' : Fin (r + 1) → V) (Λ : Submodule M.L.O V)
    (hT : LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) :
    LocNG.IsTermOver P d' (⟨LocNG.img g Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
  letI := hM.loc
  haveI := hM.char0
  have hT0 := hT
  obtain ⟨-, -, ⟨n, hn, hf, hΛn⟩, ⟨n', hn', hf', hΛn'⟩, -⟩ := hT
  change f = _ at hf
  change f' = _ at hf'
  change Λ = _ at hΛn
  change Λ = _ at hΛn'
  subst hf hf'
  have hW := (GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' Λ).1 ⟨hT0, hn, hn', hΛn, hΛn'⟩
  obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hg
  rw [hmv, ← GlobalTheory.HL.CoordTerm.lat_img c] at hW'
  have e1 : c.grp (c.grp.symm m) = m := c.grp.apply_symm_apply m
  have e2 : c.grp (c.grp.symm m') = m' := c.grp.apply_symm_apply m'
  rw [← e1, ← e2] at hW'
  have hR := ((GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d' (c.grp.symm m) (c.grp.symm m') (LocNG.img g Λ)).2 hW').1
  have k1 : (fun b => c.grp.symm m (P.A.f b)) = fun b => n (P.A.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq, e1, hm b]
  have k2 : (fun b => c.grp.symm m' (P.B.f b)) = fun b => n' (P.B.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq, e2, hm' b]
  rw [k1, k2] at hR
  exact hR

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP f f' ⟨n, hn, hf⟩ ⟨n', hn', hf'⟩ g hg d d' hmv
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  obtain ⟨hU, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, hMv, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh := (hU g).1 hg
  have hmv' := (hMv g hg d d').1 hmv
  have fixv : ∀ x : V, c.e x ∈ S.ME → g x = x := by
    intro x hx
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh _ hx
  have hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b := by
    intro b
    subst hf hf'
    refine ⟨fixv _ ?_, fixv _ ?_⟩
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq]
      exact Submodule.mem_sup_left (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn)
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f b))
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq]
      exact Submodule.mem_sup_right (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn')
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f' b))
  have hginv : c.grp g⁻¹ ∈ S.H0 := by rw [map_inv]; exact S.H0.inv_mem hh
  have hmvinv : c.grp g⁻¹ • c.dat d' = c.dat d := by
    rw [← hmv', map_inv, inv_smul_smul]
  have hback : ∀ Λ : Submodule M.L.O V, LocNG.img g (LocNG.img g⁻¹ Λ) = Λ := by
    intro Λ
    rw [← GlobalTheory.HL.CoordTerm.lat_inj c, GlobalTheory.HL.CoordTerm.lat_img, GlobalTheory.HL.CoordTerm.lat_img, map_inv,
      smul_inv_smul]
  refine ⟨hfix, ?_⟩
  ext Λ
  constructor
  · rintro ⟨Λ0, ⟨hT, hB⟩, rfl⟩
    exact ⟨fwd hM P S c g hh d d' hmv' f f' Λ0 hT, by rwa [bbne_img g f f' hfix]⟩
  · rintro ⟨hT, hB⟩
    refine ⟨LocNG.img g⁻¹ Λ, ⟨fwd hM P S c g⁻¹ hginv d' d hmvinv f f' Λ hT, ?_⟩, hback Λ⟩
    rw [← bbne_img g f f' hfix, hback Λ]
    exact hB

end GlobalTheory.HL.ComplMove
end

