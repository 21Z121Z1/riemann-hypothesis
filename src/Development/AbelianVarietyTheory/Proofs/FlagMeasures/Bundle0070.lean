import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumRestrictSlice
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Slice

theorem exists_smul_eq_out (G : Type) {α : Type} [Group G] [MulAction G α] (x : α) :
    ∃ g : G, g • x = Quotient.out (Quotient.mk (MulAction.orbitRel G α) x) := by
  have h : (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel G α) x)) x :=
    Quotient.exact (Quotient.out_eq _)
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)

theorem card_stabilizer_smul (G : Type) {α : Type} [Group G] [MulAction G α] (g : G) (x : α) :
    ENat.card (MulAction.stabilizer G (g • x)) = ENat.card (MulAction.stabilizer G x) := by
  have h : (MulAction.orbitRel G α) (g • x) x :=
    MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g)
  exact ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

theorem card_stabilizer_subgroup {G α : Type} [Group G] [MulAction G α] (H : Subgroup G) (x : α)
    (h : ∀ g : G, g • x = x → g ∈ H) :
    ENat.card (MulAction.stabilizer H x) = ENat.card (MulAction.stabilizer G x) :=
  ENat.card_congr
    { toFun := fun a => ⟨(a.1 : G), a.2⟩
      invFun := fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem orbSum_restrict : ∀ (G α : Type) [Group G] [MulAction G α] (H : Subgroup G) (X X₀ : Set α) (N : α → ℝ≥0∞), X₀ ⊆ X → Stable G X → Stable H X₀ → (∀ (g : G) x, N (g • x) = N x) → (∀ x ∈ X, ∃ g : G, g • x ∈ X₀) → (∀ (g : G), ∀ x ∈ X₀, g • x ∈ X₀ → g ∈ H) → orbSum H X₀ N = orbSum G X N := by
  intro G α _ _ H X X₀ N hsub hX hX₀ hN hmeet hret
  let f : {q : MulAction.orbitRel.Quotient H α // Quotient.out q ∈ X₀} →
      {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X} := fun q =>
    ⟨Quotient.mk (MulAction.orbitRel G α) (Quotient.out q.1), by
      obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
      rw [← hg]
      exact hX g _ (hsub q.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (MulAction.orbitRel G α) (Quotient.out a.1) (Quotient.out b.1) :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h1)
    have hgH : g ∈ H := hret g _ b.2 (hg ▸ a.2)
    have h2 : (MulAction.orbitRel H α) (Quotient.out a.1) (Quotient.out b.1) :=
      MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, hg⟩)
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq b.1]
    exact Quotient.sound h2
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hmeet _ b.2
    obtain ⟨k, hk⟩ := exists_smul_eq_out H (g • Quotient.out b.1)
    refine ⟨⟨Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1), ?_⟩, ?_⟩
    · rw [← hk]; exact hX₀ k _ hg
    · apply Subtype.ext
      show Quotient.mk (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1))) = b.1
      rw [← hk]
      conv_rhs => rw [← Quotient.out_eq b.1]
      apply Quotient.sound
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨(k : G) * g, ?_⟩)
      rw [mul_smul]; rfl
  unfold orbSum
  rw [← (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
  have e : Quotient.out ((Equiv.ofBijective f ⟨hinj, hsurj⟩) q).1 = g • Quotient.out q.1 := hg.symm
  rw [e, hN, card_stabilizer_smul, card_stabilizer_subgroup H _
    (fun a ha => hret a _ q.2 (by rw [ha]; exact q.2))]

end GlobalTheory.Mass.Slice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariant
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbTransport

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma exists_smul_eq_orbit_out {G α : Type} [Group G] [MulAction G α] (y : α) :
    ∃ g : G, g • y = (Quotient.mk (orbitRel G α) y).out := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G α) y
  exact ⟨g, hg⟩

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma card_stabilizer_smul_eq' {G α : Type} [Group G] [MulAction G α] (g : G) (a : α) :
    ENat.card (stabilizer G (g • a)) = ENat.card (stabilizer G a) :=
  (ENat.card_congr (stabilizerEquivStabilizer (g := g) rfl).toEquiv).symm

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in

theorem _root_.GlobalTheory.Mass.OrbTransport.main : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by
  intro G G' α β _ _ _ _ φ f X Y N hX hY hf hequiv hN
  have hcard : ∀ x ∈ X, ENat.card (stabilizer G' (f x)) = ENat.card (stabilizer G x) := by
    intro x hx
    refine (ENat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun g => ?_)).symm
    simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← hequiv g x hx]
    exact ⟨fun h => by rw [h], fun h => hf.injOn (hX g x hx) hx h⟩
  have hout : ∀ q : {q : orbitRel.Quotient G α // q.out ∈ X},
      (Quotient.mk (orbitRel G' β) (f q.1.out)).out ∈ Y := by
    intro q
    obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
    rw [← hg]
    exact hY g _ (hf.mapsTo q.2)
  let F : {q : orbitRel.Quotient G α // q.out ∈ X} → {q : orbitRel.Quotient G' β // q.out ∈ Y} :=
    fun q => ⟨Quotient.mk _ (f q.1.out), hout q⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
      obtain ⟨g', hg'⟩ := Quotient.exact (congrArg Subtype.val h)
      apply Subtype.ext
      show q₁ = q₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      apply Quotient.sound
      refine ⟨φ.symm g', ?_⟩
      apply hf.injOn (hX _ _ h₂) h₁
      rw [hequiv _ _ h₂, MulEquiv.apply_symm_apply]
      exact hg'
    · rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hfx⟩ := hf.surjOn hq'
      obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G) x
      have hmem : (Quotient.mk (orbitRel G α) x).out ∈ X := by rw [← hg]; exact hX g x hx
      refine ⟨⟨Quotient.mk _ x, hmem⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (f (Quotient.mk (orbitRel G α) x).out) = q'
      rw [← Quotient.out_eq q', ← hg, hequiv g x hx, hfx]
      exact Quotient.sound ⟨φ g, rfl⟩
  unfold _root_.GlobalTheory.Mass.orbSum
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  congr 1
  funext q
  obtain ⟨g', hg'⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
  show _ = (ENat.card (stabilizer G' (Quotient.mk (orbitRel G' β) (f q.1.out)).out) : ℝ≥0∞)⁻¹ *
    N (Quotient.mk (orbitRel G' β) (f q.1.out)).out
  rw [← hg', card_stabilizer_smul_eq', hN, hcard _ q.2]

end GlobalTheory.Mass.OrbTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentatives
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypeRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem h_add_left (a b y : S.V) : S.h (a + b) y = S.h a y + S.h b y := by
  simp only [Frames.h, hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem h_add_right (a y z : S.V) : S.h a (y + z) = S.h a y + S.h a z := by
  simp only [Frames.h, hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem h_smul_left (c : E) (a y : S.V) : S.h (c • a) y = c * S.h a y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem h_smul_right (c : E) (a y : S.V) : S.h a (c • y) = L.cj c * S.h a y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem h_zero_left' (y : S.V) : S.h 0 y = 0 := by
  simp [Frames.h, hf]

private theorem h_zero_right_flag_measures (a : S.V) : S.h a 0 = 0 := by
  simp [Frames.h, hf]

private theorem h_eq_zero_of_span_orth {s t : Set S.V} (hst : ∀ a ∈ s, ∀ b ∈ t, S.h a b = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E s) (hy : y ∈ Submodule.span E t) : S.h x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb => exact hst a ha b hb
    | zero => exact h_zero_right_flag_measures S a
    | add u v _ _ hu hv => rw [h_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [h_smul_right, hu, mul_zero]
  | zero => exact h_zero_left' S y
  | add u v _ _ hu hv => rw [h_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [h_smul_left, hu, mul_zero]

theorem iso_of (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    {x y : S.V} (hx : x ∈ S.spanTo g r) (hy : y ∈ S.spanTo g r) : S.h x y = 0 := by
  unfold Frames.spanTo at hx hy
  refine h_eq_zero_of_span_orth S ?_ hx hy
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  change hf L S.Hm (g i) (g j) = 0
  rw [hg, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

theorem spanTo_mono (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)

theorem disj (hli : LinearIndependent E (Sum.elim S.f S.f')) :
    Disjoint (S.spanTo S.f (r + 1)) (S.spanTo S.f' (r + 1)) := by
  have h := (linearIndependent_sum.1 hli).2.2
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  unfold Frames.spanTo
  exact h.mono (Submodule.span_mono (Set.image_subset_range _ _))
    (Submodule.span_mono (Set.image_subset_range _ _))

theorem frame_split (Λ : Submodule L.O S.V) (g g' : Fin (r + 1) → S.V) (h0 : S.th ≠ 0)
    (hg : ∀ b, g b ∈ S.spanTo S.f (r + 1))
    (hg' : ∀ b, g' b ∈ Λ ∧ g' b ∈ S.spanTo S.f' (r + 1)) {m : S.V} (hm : m ∈ S.Mof g g') :
    ∃ a ∈ S.spanTo S.f (r + 1), ∃ a' ∈ S.spanTo S.f' (r + 1), a' ∈ Λ ∧
      algebraMap F E S.th • m = a + a' := by
  have hinv : ∀ v : S.V, algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
    intro v
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨algebraMap F E S.th • g b, Submodule.smul_mem _ _ (hg b), 0, Submodule.zero_mem _,
        Submodule.zero_mem _, by rw [add_zero]⟩
    · refine ⟨-g b, Submodule.neg_mem _ (hg b), g' b, (hg' b).2, (hg' b).1, ?_⟩
      dsimp only
      rw [hinv]
      abel
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    obtain ⟨b, hb, b', hb', hΛ', he'⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb',
      Submodule.add_mem _ hΛ hΛ', by rw [smul_add, he, he']; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    refine ⟨(c : E) • a, Submodule.smul_mem _ _ ha, (c : E) • a', Submodule.smul_mem _ _ ha',
      Λ.smul_mem c hΛ, ?_⟩
    rw [Subring.smul_def, smul_comm, he, smul_add]

private theorem algebraMap_mem_O_of_mem_valuationInteger (L : LocE F E) {x : F} (hx : x ∈ 𝒪[F]) : algebraMap F E x ∈ L.O := by
  rw [L.O_def]
  have := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨x, hx⟩)
  convert this using 1
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rfl

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB B₀ hB₀ hrep hpair
  obtain ⟨hli, -, -, -, -, h0, hthF, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hSD, -, hMsat, hfr, hfr', -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT).2.1
  have hthO : algebraMap F E S.th ∈ L.O := algebraMap_mem_O_of_mem_valuationInteger L hthF
  have hcj : L.cj (algebraMap F E S.th) = algebraMap F E S.th := L.cj.commutes S.th
  have hinv : ∀ v : S.V, algebraMap F E S.th⁻¹ • algebraMap F E S.th • v = v := by
    intro v
    rw [smul_smul, ← map_mul, inv_mul_cancel₀ h0, map_one, one_smul]
  have hint : ∀ v ∈ Λ, ∀ w ∈ Λ, S.h v w ∈ L.O := fun v hv w hw => (hSD.2 w).2 hw v hv
  have hXX : ∀ v ∈ S.X, ∀ w ∈ S.X, S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f (-algebraMap F E S.T) S.gram hv hw
  have hXX' : ∀ v ∈ S.X', ∀ w ∈ S.X', S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f' (-algebraMap F E S.T') S.gram' hv hw
  have hXME : S.X ≤ S.ME := (spanTo_mono S S.f).trans le_sup_left
  have hX'ME : S.X' ≤ S.ME := (spanTo_mono S S.f').trans le_sup_right
  have hsatΛ : S.sat Λ ≤ Λ := inf_le_left
  have hg : ∀ b, S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    ((hfr (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))).2
  have hg' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (hfr' (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))
  have hdisj := Submodule.disjoint_def.1 (disj S hli)
  have key : ∀ x ∈ S.X, ∀ x' ∈ S.X', S.InTh Λ (x + x') → ∃ u ∈ S.X, ∃ u' ∈ S.X',
      u + u' ∈ B₀ ∧ u + u' ∈ Λ ∧ x' - algebraMap F E S.th • u' ∈ Λ ∧
      ∃ m ∈ Λ, (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • m := by
    rintro x hx x' hx' ⟨y, hyΛ, hxy⟩
    have hyME : y ∈ S.ME := by
      rw [← hinv y, ← hxy]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hXME hx) (hX'ME hx'))
    have hysat : y ∈ S.sat Λ := Submodule.mem_inf.2 ⟨hyΛ, hyME⟩
    obtain ⟨y₀, hy₀, hmM⟩ := hrep y hysat
    obtain ⟨hy₀Λ, hy₀X⟩ := hB₀ y₀ hy₀
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy₀X
    have hmΛ : y - (u + u') ∈ Λ := hsatΛ (hMsat hmM)
    obtain ⟨b, hb, b', hb', hb'Λ, hbb⟩ := frame_split S Λ _ _ h0 hg hg' hmM
    have hsum : (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • (y - (u + u')) := by
      rw [smul_sub, ← hxy, smul_add]
      abel
    have hdiff : b' - (x' - algebraMap F E S.th • u') = 0 := by
      apply hdisj
      · have he : b' - (x' - algebraMap F E S.th • u') = (x - algebraMap F E S.th • u) - b := by
          have h2 := hsum.trans hbb
          linear_combination -h2
        rw [he]
        exact Submodule.sub_mem _
          (spanTo_mono S S.f (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu))) hb
      · exact Submodule.sub_mem _ hb'
          (spanTo_mono S S.f' (Submodule.sub_mem _ hx' (Submodule.smul_mem _ _ hu')))
    have ha' : x' - algebraMap F E S.th • u' = b' := (sub_eq_zero.1 hdiff).symm
    exact ⟨u, hu, u', hu', hy₀, hy₀Λ, by rw [ha']; exact hb'Λ, y - (u + u'), hmΛ, hsum⟩
  refine ⟨hB, ?_, ?_⟩
  · intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
    exact (hlev y hy r).2 ⟨y₀, (hB₀ y₀ hy₀).2, hm⟩
  · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2
    obtain ⟨u₁, hu₁, u₁', hu₁', hB1, hy1, ha1', m₁, hm₁, he1⟩ := key x₁ hx₁ x₁' hx₁' h1
    obtain ⟨u₂, hu₂, u₂', hu₂', hB2, hy2, ha2', m₂, hm₂, he2⟩ := key x₂ hx₂ x₂' hx₂' h2
    generalize ht : algebraMap F E S.th = t at *
    set a₁ := x₁ - t • u₁ with ha₁
    set a₁' := x₁' - t • u₁' with ha₁d
    set a₂' := x₂' - t • u₂' with ha₂d
    have ha₁X : a₁ ∈ S.X := Submodule.sub_mem _ hx₁ (Submodule.smul_mem _ _ hu₁)
    have ha₁'X : a₁' ∈ S.X' := Submodule.sub_mem _ hx₁' (Submodule.smul_mem _ _ hu₁')
    have ha₂'X : a₂' ∈ S.X' := Submodule.sub_mem _ hx₂' (Submodule.smul_mem _ _ hu₂')
    have hB1' : algebraMap F E S.th⁻¹ • (t • u₁ + t • u₁') ∈ B₀ := by rw [← smul_add, hinv]; exact hB1
    have hB2' : algebraMap F E S.th⁻¹ • (t • u₂ + t • u₂') ∈ B₀ := by rw [← smul_add, hinv]; exact hB2
    obtain ⟨c₀, hc₀, hc₀e⟩ := hpair (t • u₁) (Submodule.smul_mem _ _ hu₁) (t • u₁')
      (Submodule.smul_mem _ _ hu₁') (t • u₂) (Submodule.smul_mem _ _ hu₂) (t • u₂')
      (Submodule.smul_mem _ _ hu₂') hB1' hB2'
    have ex₁ : x₁ = t • u₁ + a₁ := by rw [ha₁]; abel
    have ex₂' : x₂' = t • u₂' + a₂' := by rw [ha₂d]; abel
    have eA : S.h x₁ x₂' = S.h (t • u₁) (t • u₂') + S.h (t • u₁) a₂' + S.h a₁ (t • u₂') +
        S.h a₁ a₂' := by
      rw [ex₁, ex₂', h_add_left, h_add_right, h_add_right]
      ring
    have eB : S.h (t • u₁) a₂' = t * S.h u₁ a₂' := h_smul_left S _ _ _
    have eC : S.h (u₁ + u₁') a₂' = S.h u₁ a₂' + S.h u₁' a₂' := h_add_left S _ _ _
    have eD : S.h u₁' a₂' = 0 := hXX' _ hu₁' _ ha₂'X
    have eE : S.h a₁ (t • u₂') = t * S.h a₁ u₂' := by rw [h_smul_right, hcj]
    have eF : S.h a₁ (u₂ + u₂') = S.h a₁ u₂ + S.h a₁ u₂' := h_add_right S _ _ _
    have eG : S.h a₁ u₂ = 0 := hXX _ ha₁X _ hu₂
    have eH : S.h (a₁ + a₁') a₂' = S.h a₁ a₂' + S.h a₁' a₂' := h_add_left S _ _ _
    have eI : S.h (t • m₁) a₂' = t * S.h m₁ a₂' := h_smul_left S _ _ _
    have eJ : S.h a₁' a₂' = 0 := hXX' _ ha₁'X _ ha₂'X
    have eK : S.h (t • m₁) (u₂ + u₂') = t * S.h m₁ (u₂ + u₂') := h_smul_left S _ _ _
    have eL : S.h (a₁ + a₁') (u₂ + u₂') = S.h a₁ (u₂ + u₂') + S.h a₁' (u₂ + u₂') :=
      h_add_left S _ _ _
    rw [he1] at eH eL
    have hO1 : S.h (u₁ + u₁') a₂' ∈ L.O := hint _ hy1 _ ha2'
    have hO2 : S.h m₁ (u₂ + u₂') ∈ L.O := hint _ hm₁ _ hy2
    have hO3 : S.h a₁' (u₂ + u₂') ∈ L.O := hint _ ha1' _ hy2
    have hO4 : S.h m₁ a₂' ∈ L.O := hint _ hm₁ _ ha2'
    refine ⟨c₀ + S.h (u₁ + u₁') a₂' + (t * S.h m₁ (u₂ + u₂') - S.h a₁' (u₂ + u₂')) + S.h m₁ a₂',
      ?_, ?_⟩
    · exact L.O.add_mem (L.O.add_mem (L.O.add_mem hc₀ hO1)
        (L.O.sub_mem (L.O.mul_mem hthO hO2) hO3)) hO4
    · rw [eA, hc₀e]
      linear_combination eB - t * eC - t * eD + eE - t * eF - t * eG - eH + eI - eJ + t * eK - t * eL

end GlobalTheory.HL.TypeRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximation
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PatternApprox

theorem exists_clear {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [CommRing Ep] [Algebra Fp Ep] [Module.Finite Fp Ep]
    (O : Subring Ep) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[Fp] x) {ι : Type} [Fintype ι] (x : ι → Ep) :
    ∃ a : Fp, a ≠ 0 ∧ ∀ i, algebraMap Fp Ep a * x i ∈ O := by
  have hfr : IsFractionRing 𝒪[Fp] Fp := (Valuation.integer.integers (valuation Fp)).isFractionRing
  have halg : ∀ i, IsAlgebraic 𝒪[Fp] (x i) := fun i =>
    (IsFractionRing.isAlgebraic_iff 𝒪[Fp] Fp Ep).mpr (Algebra.IsIntegral.isIntegral (R := Fp) (x i)).isAlgebraic
  choose y hy0 hyi using fun i => (halg i).exists_integral_multiple
  have hym : ∀ k, algebraMap Fp Ep (y k : Fp) ∈ O := fun k => by
    rw [hO, show algebraMap Fp Ep (y k : Fp) = algebraMap 𝒪[Fp] Ep (y k) from
      (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y k)).symm]
    exact isIntegral_algebraMap
  refine ⟨∏ k, (y k : Fp), ?_, fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hy0 k (Subtype.ext (by simpa using h))
  · have h1 : algebraMap Fp Ep (y i : Fp) * x i ∈ O := by
      rw [hO, show algebraMap Fp Ep (y i : Fp) = algebraMap 𝒪[Fp] Ep (y i) from
        (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y i)).symm, ← Algebra.smul_def]
      exact hyi i
    rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k _ => hym k) h1

variable {R : Type} [CommRing R]

theorem det_eq_one {m : ℕ} (I : Fin m → Fin m → Prop) (hI : ∀ i j, I i j → i < j)
    (s : Matrix (Fin m) (Fin m) R) (hs : ∀ i j, ¬ I i j → s i j = if i = j then 1 else 0) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [hs i i (fun h => lt_irrefl i (hI i i h))]
    simp
  · intro i j hji
    rw [hs i j (fun h => lt_asymm (hI i j h) hji)]
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    simp [hne]

theorem adjugate_mem {m : ℕ} (O : Subring R) (s : Matrix (Fin m) (Fin m) R) (h : ∀ i j, s i j ∈ O) :
    ∀ i j, s.adjugate i j ∈ O := by
  let S : Matrix (Fin m) (Fin m) O := fun i j => ⟨s i j, h i j⟩
  have hS : O.subtype.mapMatrix S = s := by ext i j; rfl
  intro i j
  rw [← hS, ← RingHom.map_adjugate]
  exact (S.adjugate i j).2

end GlobalTheory.HL.PatternApprox

open GlobalTheory.HL.PatternApprox in

theorem GlobalTheory.HL.pattern_strong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A m I hlt _htr c hc s hs hsint
  have hinv : ∀ p, (s p)⁻¹ = (s p).adjugate := fun p => by
    rw [Matrix.inv_def, det_eq_one I hlt (s p) (hs p), Ring.inverse_one, one_smul]
  have hcl : ∀ p, ∃ a : ((A.loc p).Fp)ˣ, (IsIntM (A.L p) (s p) → a = 1) ∧
      ∀ i j, algebraMap (A.loc p).Fp (A.loc p).Ep (a : (A.loc p).Fp) * (s p)⁻¹ i j ∈ (A.L p).O := by
    intro p
    haveI := (A.loc p).lf
    haveI : Module.Free (A.loc p).Fp (A.loc p).Ep := (A.loc p).free
    haveI : Module.Finite (A.loc p).Fp (A.loc p).Ep := Module.finite_of_finrank_eq_succ (A.loc p).rank
    by_cases h : IsIntM (A.L p) (s p)
    · refine ⟨1, fun _ => rfl, fun i j => ?_⟩
      rw [Units.val_one, map_one, one_mul, hinv p]
      exact adjugate_mem (A.L p).O (s p) h i j
    · obtain ⟨a, ha0, ha⟩ := exists_clear (A.L p).O (A.L p).O_def
        (fun ij : Fin m × Fin m => (s p)⁻¹ ij.1 ij.2)
      exact ⟨Units.mk0 a ha0, fun h' => absurd h' h, fun i j => ha (i, j)⟩
  choose c' hc'1 hc'2 using hcl
  let d : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * c' p
  have hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite := by
    apply (hc.union hsint).subset
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨u, hu⟩, hint⟩ := hno
    exact hp ⟨u, by simp [d, hc'1 p hint, hu]⟩
  have hap := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.1
  have hx : ∀ i j, ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - s p i j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o :=
    fun i j => hap (fun p => s p i j) (hsint.subset fun p hp hi => hp (hi i j))
  choose x hx using hx
  refine ⟨fun i j => if I i j then x i j else if i = j then 1 else 0, fun i j h => by simp [h], fun p i j => ?_⟩
  set t : Matrix (Fin m) (Fin m) E := fun i j => if I i j then x i j else if i = j then 1 else 0 with ht
  have hD : ∀ k l, ∃ o ∈ (A.L p).O, (t.map (A.loc p).ιE - s p) k l =
      algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro k l
    by_cases hkl : I k l
    · obtain ⟨o, ho, he⟩ := hx k l p
      refine ⟨o, ho, ?_⟩
      rw [← he]
      show (A.loc p).ιE (t k l) - s p k l = (A.loc p).ιE (x k l) - s p k l
      rw [ht]
      simp only [hkl, if_true]
    · refine ⟨0, (A.L p).O.zero_mem, ?_⟩
      rw [Matrix.sub_apply, Matrix.map_apply, hs p k l hkl, mul_zero]
      simp only [ht, hkl, if_false]
      split_ifs <;> simp
  choose o ho hoeq using hD
  have hunit : (s p)⁻¹ * s p = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_eq_one I hlt (s p) (hs p)]; exact isUnit_one)
  have heq : (s p)⁻¹ * t.map (A.loc p).ιE - 1 = (s p)⁻¹ * (t.map (A.loc p).ιE - s p) := by
    rw [Matrix.mul_sub, hunit]
  refine ⟨∑ k, (algebraMap (A.loc p).Fp (A.loc p).Ep (c' p : (A.loc p).Fp) * (s p)⁻¹ i k) * o k j,
    (A.L p).O.sum_mem fun k _ => (A.L p).O.mul_mem (hc'2 p i k) (ho k j), ?_⟩
  rw [heq, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hoeq k j]
  simp only [d, Units.val_mul, map_mul]
  ring
end

