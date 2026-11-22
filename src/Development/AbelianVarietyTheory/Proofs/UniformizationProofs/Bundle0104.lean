import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistGen

open LBGerm TopologicalSpace

variable {X : Scheme.{0}} {M H : LB X}

theorem gm_tw_g (M H : LB X) (t : ℕ) (y : X) (p q : M.ι × H.ι) (hp : y ∈ M.U p.1 ⊓ H.U p.2)
    (hq : y ∈ M.U q.1 ⊓ H.U q.2) :
    (gm (𝟙 X) y ((tw M H t).U p ⊓ (tw M H t).U q) ((tw M H t).g p q)).val =
      (gm (𝟙 X) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1)).val *
        (gm (𝟙 X) y (H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2)).val ^ t := by
  have hy : (𝟙 X : X ⟶ X) y ∈ M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) := ⟨hp, hq⟩
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, tw_g]
  refine congrArg Units.val ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _) ?_))
  rw [zpow_natCast]
  exact (map_pow _ _ _).trans (congrArg (· ^ t) (gm_res (𝟙 X) y _ hy _))

theorem exists_mul_pow (a e : ℕ) (u : LB.Sec (tw M H a)) (s : LB.Sec H) :
    ∃ u' : LB.Sec (tw M H ((a + e : ℕ) : ℤ)), nonzeroLocus u ⊓ nonzeroLocus s ≤ nonzeroLocus u' := by
  let F : ∀ p : M.ι × H.ι, Γ(X, M.U p.1 ⊓ H.U p.2) := fun p =>
    (show Γ(X, M.U p.1 ⊓ H.U p.2) from u.f p) * resG X inf_le_right (s.f p.2) ^ e
  have hF : ∀ (y : X) (p : M.ι × H.ι), y ∈ M.U p.1 ⊓ H.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f p) * gs (𝟙 X) y _ (s.f p.2) ^ e := fun y p hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨secOfGerm (M := tw M H ((a + e : ℕ) : ℤ)) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · refine (hF y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_tw_g M H (a + e) y p q hp hq) (hF y q hq)).symm)
    rw [gs_compat u (𝟙 X) y (j := p) (j' := q) hp hq, gm_tw_g M H a y p q hp hq,
      gs_compat s (𝟙 X) y (j := p.2) (j' := q.2) hp.2 hq.2]
    ring
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
    refine (mem_nonzeroLocus_iff_isUnit (M := tw M H ((a + e : ℕ) : ℤ)) _ (k := p) hp).2 ?_
    refine (congrArg IsUnit (hF y p hp)).mpr ?_
    exact (((mem_nonzeroLocus_iff_isUnit u hp).1 hy.1).mul
      (((mem_nonzeroLocus_iff_isUnit s hp.2).1 hy.2).pow e))

theorem exists_sec_of_le_chart [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (n : ℕ)
    (σ : ∀ j, Γ(X, H.U j))
    (hσ : ∀ (y : X) j j', y ∈ H.U j → y ∈ H.U j' → gs (𝟙 X) y _ (σ j) =
      (gm (𝟙 X) y (H.U j ⊓ H.U j') (H.g j j')).val ^ n * gs (𝟙 X) y _ (σ j'))
    (V : X.Opens) (hV : ∀ (y : X) j, y ∈ H.U j → (y ∈ V ↔ IsUnit (gs (𝟙 X) y _ (σ j))))
    (k : M.ι) (hk : V ≤ M.U k) :
    ∃ (N : ℕ) (u : LB.Sec (tw M H ((n * N : ℕ) : ℤ))), V ≤ nonzeroLocus u := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → M.ι × H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (J a).1 ⊓ H.U (J a).2) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_tw hM hH 0)
  have hW₂ : ∀ a, W a ≤ H.U (J a).2 := fun a => (hW a).trans inf_le_right
  have hb : ∀ (U : X.Opens) (j : H.ι) (hU : U ≤ H.U j) (y : X),
      y ∈ X.basicOpen (resG X hU (σ j)) → y ∈ V := fun U j hU y hy => by
    have hy₁ : y ∈ U := X.basicOpen_le _ hy
    have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
    rwa [gs_res _ y _ hy₁, ← hV y j (hU hy₁)] at hs
  have step₁ : ∀ a, ∃ (e : ℕ) (v : Γ(X, W a)), ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ v = gs (𝟙 X) y _ (σ (J a).2) ^ e *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val := fun a => by
    have le : X.basicOpen (resG X (hW₂ a) (σ (J a).2)) ≤ M.U (J a).1 ⊓ M.U k :=
      fun y hy => ⟨(hW a (X.basicOpen_le _ hy)).1, hk (hb _ _ _ y hy)⟩
    obtain ⟨e, v, hv⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (W a) (hWa a).isCompact
      (hWa a).isQuasiSeparated (resG X (hW₂ a) (σ (J a).2)) (resG X le (M.g (J a).1 k).val)
    have hv' : resG X (X.basicOpen_le _) v =
        resG X (X.basicOpen_le _) (resG X (hW₂ a) (σ (J a).2)) ^ e * resG X le (M.g (J a).1 k).val := hv
    refine ⟨e, v, fun y hy hs => ?_⟩
    have hy' : y ∈ X.basicOpen (resG X (hW₂ a) (σ (J a).2)) := (isUnit_gs_iff (𝟙 X) y _ hy _).1 (by
      rw [gs_res _ y _ hy]; exact (hV y _ (hW₂ a hy)).1 hs)
    have e₁ := congrArg (gs (𝟙 X) y _) hv'
    rwa [gs_res _ y _ hy', gs_mul _ y _ hy', gs_pow _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy,
      gs_res _ y _ hy', gs_unit (𝟙 X) y _ (le hy')] at e₁
  choose e v hv using step₁
  obtain ⟨N₁, v', hv'⟩ : ∃ (N₁ : ℕ) (v' : ∀ a, Γ(X, W a)), ∀ a, ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ (v' a) = gs (𝟙 X) y _ (σ (J a).2) ^ N₁ *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val :=
    ⟨Finset.univ.sup e, fun a => resG X (hW₂ a) (σ (J a).2) ^ (Finset.univ.sup e - e a) * v a, fun a y hy hs => by
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hv a y hy hs, ← _root_.mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ a))]⟩
  have step₂ : ∀ p : α × α, ∃ d : ℕ, ∀ y ∈ W p.1 ⊓ W p.2, gs (𝟙 X) y _ (σ (J p.1).2) ^ d *
      (gs (𝟙 X) y _ (v' p.1) - (gm (𝟙 X) y (M.U (J p.1).1 ⊓ M.U (J p.2).1) (M.g (J p.1).1 (J p.2).1)).val *
        (gm (𝟙 X) y (H.U (J p.1).2 ⊓ H.U (J p.2).2)
        (H.g (J p.1).2 (J p.2).2)).val ^ (n * N₁) * gs (𝟙 X) y _ (v' p.2)) = 0 := by
    rintro ⟨a, b⟩
    have hcpt : IsCompact ((W a ⊓ W b : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hWa a).isCompact (W b).isOpen (hWa b).isCompact
    have le₁ : W a ⊓ W b ≤ M.U (J a).1 ⊓ M.U (J b).1 := fun y hy => ⟨(hW a hy.1).1, (hW b hy.2).1⟩
    have le : W a ⊓ W b ≤ H.U (J a).2 ⊓ H.U (J b).2 := fun y hy => ⟨(hW a hy.1).2, (hW b hy.2).2⟩
    have hx : ∀ y ∈ W a ⊓ W b, gs (𝟙 X) y (W a ⊓ W b) (resG X inf_le_left (v' a) -
        resG X le₁ (M.g (J a).1 (J b).1).val * resG X le (H.g (J a).2 (J b).2).val ^ (n * N₁) *
          resG X inf_le_right (v' b)) =
        gs (𝟙 X) y _ (v' a) - (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U (J b).1) (M.g (J a).1 (J b).1)).val *
          (gm (𝟙 X) y (H.U (J a).2 ⊓ H.U (J b).2) (H.g (J a).2 (J b).2)).val ^ (n * N₁) *
            gs (𝟙 X) y _ (v' b) := fun y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_res _ y _ hy, gs_res _ y _ hy, gs_unit (𝟙 X) y _ (le hy), gs_unit (𝟙 X) y _ (le₁ hy)]
    obtain ⟨d, hd⟩ := exists_pow_mul_gs_eq_zero hcpt (resG X (inf_le_left.trans (hW₂ a)) (σ (J a).2)) _
      fun y hy => by
        have hy₁ : y ∈ W a ⊓ W b := X.basicOpen_le _ hy
        have hs := hb _ _ _ y hy
        refine (hx y hy₁).trans ?_
        rw [hv' a y hy₁.1 hs, hv' b y hy₁.2 hs, hσ y (J a).2 (J b).2 (hW₂ a hy₁.1) (hW₂ b hy₁.2),
          ← gm_cocycle hM (𝟙 X) y (hW a hy₁.1).1 (hW b hy₁.2).1 (hk hs), Units.val_mul]
        ring
    refine ⟨d, fun y hy => ?_⟩
    have := hd y hy
    rwa [hx y hy, gs_res _ y _ hy] at this
  choose d hd using step₂
  obtain ⟨c, hc'⟩ : ∃ c, ∀ p, d p ≤ c := ⟨Finset.univ.sup d, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  have hz : ∀ a, ∀ y ∈ W a, gs (𝟙 X) y _ (resG X (hW₂ a) (σ (J a).2) ^ c * v' a) =
      gs (𝟙 X) y _ (σ (J a).2) ^ c * gs (𝟙 X) y _ (v' a) := fun a y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨u, hu⟩ := exists_sec_of_refinement (isLB_tw hM hH ((n * (N₁ + c) : ℕ) : ℤ)) W J hW hc
    (fun a => resG X (hW₂ a) (σ (J a).2) ^ c * v' a) fun y a b ha hb => by
      obtain ⟨c', hc''⟩ := Nat.exists_eq_add_of_le (hc' (a, b))
      have e₁ := hd (a, b) y ⟨ha, hb⟩
      have e₂ := hσ y (J a).2 (J b).2 (hW₂ a ha) (hW₂ b hb)
      rw [hz a y ha, hz b y hb, gm_tw_g M H _ y (J a) (J b) (hW a ha) (hW b hb)]
      dsimp only at e₁
      rw [e₂] at e₁ ⊢
      rw [hc'']
      generalize gs (𝟙 X) y _ (σ (J b).2) = τ at e₁ ⊢
      generalize Units.val (gm (𝟙 X) y _ (H.g (J a).2 (J b).2)) = w at e₁ ⊢
      linear_combination (w ^ n * τ) ^ c' * e₁
  refine ⟨N₁ + c, u, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  have hs := (hV y _ (hW₂ a ha)).1 hy
  rw [mem_nonzeroLocus_iff_isUnit u (k := J a) (hW a ha), hu y (J a) a (hW a ha) ha, hz a y ha, hv' a y ha hy]
  exact (Units.isUnit _).mul ((hs.pow c).mul ((hs.pow N₁).mul (Units.isUnit _)))

theorem compact_quasiSeparated (hH : H.IsLB) {I : Type} [Finite I] (s : I → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  have mem : ∀ y : X, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hc]; trivial)
  refine ⟨⟨?_⟩, quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_⟩
  · have : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) :=
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (mem y)).symm
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isCompact
  · have : (U.1 ∩ V.1 : Set X) = ⋃ i, ((nonzeroLocus (s i) ⊓ U.1 : X.Opens) : Set X) ∩
        ((nonzeroLocus (s i) ⊓ V.1 : X.Opens) : Set X) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨i, hi⟩ := mem y
        exact Set.mem_iUnion.2 ⟨i, ⟨hi, hy.1⟩, ⟨hi, hy.2⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        exact ⟨hi.1.2, hi.2.2⟩
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isQuasiSeparated _ _ Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) U.2).isCompact Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) V.2).isCompact

theorem exists_nhds [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (s : LB.Sec H)
    (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧ ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hM y
  have hl := nonzeroLocus_secToPow s (le_refl 1)
  rw [← hl] at ha hy
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := M.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hH (secToPow s 1) a
  obtain ⟨N, u, hu⟩ := exists_sec_of_le_chart hM hH (1 * m) (powSecFn σ) (fun z j j' hj hj' => by
      have hz : z ∈ H.U j ⊓ H.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨X.basicOpen a, 1 * m * N, hya, fun e => ?_⟩
  obtain ⟨u', hu'⟩ := exists_mul_pow _ e u s
  exact ⟨u', (le_inf hu ((X.basicOpen_le a).trans hl.le)).trans hu'⟩

theorem twist_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (n' : ℕ) (u : Fin (n' + 1) → LB.Sec (tw M H t)), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro R _ X f H n s hH hs M hM
  obtain ⟨_, _⟩ := compact_quasiSeparated hH s hs.1 fun i => (hs.2 i).1
  have loc : ∀ y : X, ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧
      ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    exact exists_nhds hM hH (s i) (hs.2 i).1 y hi
  choose V N hy hV using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨(T.sup N : ℕ), fun t ht => ?_⟩
  have h : ∀ y : T, ∃ u : LB.Sec (tw M H t), V y ≤ nonzeroLocus u := fun y => by
    have h₁ : N y ≤ T.sup N := Finset.le_sup y.2
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = ((N y + e : ℕ) : ℤ) := ⟨(t - N y).toNat, by omega⟩
    exact hV y e
  choose u hu using h
  let c : Option T → LB.Sec (tw M H t) := fun o => o.elim DVR.SecOps.secZero u
  let e : Option T ≃ Fin (Fintype.card T + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => c (e.symm i), top_unique fun x _ => ?_⟩
  obtain ⟨y, hyT, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine Opens.mem_iSup.2 ⟨e (some ⟨y, hyT⟩), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hu ⟨y, hyT⟩ hx

end GlobalTheory.TwistGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueAbelianPartImageAdicCompletePointStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_abelianPart_image_adicComplete_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  first | exact @GlobalTheory.UU.PointImage.main | exact GlobalTheory.UU.PointImage.main | (intros; apply GlobalTheory.UU.PointImage.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatch
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ExpansionClause

theorem expBij_of_match : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  intro h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj
  have hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by
    unfold UnifPre.SecK
    rw [hM.LG]
  have hK := GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k
  have hu := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D.toPre A G U (FractionRing V) k
  have ht := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D.toPre A G U (FractionRing V) k hk
  have e1 := GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k
  have e2 := GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k
  unfold UnifPre.ExpBij
  refine ⟨fun σ => ?_, fun s => ?_⟩
  · obtain ⟨t, hσt, -⟩ := hK.1 (cast hT σ)
    obtain ⟨s, hs⟩ := ht t
    refine ⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩
    have h := (hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl
    obtain ⟨s', fe⟩ := s'
    cases h
    rfl
  · obtain ⟨t, hts⟩ := hsurj s
    obtain ⟨σ₀, hσt, huniq⟩ := hK.2 t
    refine ⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩
    obtain ⟨t', hσt', -⟩ := hK.1 (cast hT σ)
    have h := (hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl
    subst h
    rw [← huniq _ hσt']
    simp

end GlobalTheory.ExpansionClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal : ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  first | exact @GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | exact GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_localization_maximal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfectStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  first | exact @GlobalTheory.UU.generic_card_and_nondeg | exact GlobalTheory.UU.generic_card_and_nondeg | (intros; apply GlobalTheory.UU.generic_card_and_nondeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOrigin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.IndComp

section Twist

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left}

theorem twist_unique (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {n : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])}
    {t u u' : LB.Sec (LPow A L n T)} (h : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u)
    (h' : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u') : u = u' := by
  have e : ∀ j, u.f j = u'.f j := fun j => sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n)
    (fun y J hJ => (VVRank.sv_of_isTwistPull A h (𝟙 _) y hJ).trans (VVRank.sv_of_isTwistPull A h' (𝟙 _) y hJ).symm) j
  obtain ⟨a, _⟩ := u
  obtain ⟨b, _⟩ := u'
  obtain rfl : a = b := funext e
  rfl

theorem exists_twist_comp (hL : L.IsLB) (ψ ψ' : T ⊗ A ⟶ T ⊗ A) (n : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![n, -n]))
    (hα : α.IsGen) (hα' : α'.IsGen) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t u v : LB.Sec (LPow A L n T), IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t u →
        IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α u v →
        IsTwistPull A L (ψ ≫ ψ') ((ψ ≫ ψ') ≫ snd _ _) rfl n n β t v := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, Over.comp_left, Category.assoc]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ α (LB.pullGen L _ _ α' ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.pullGen_isGen _ _ _ _ hα' _))
  refine ⟨β, hβ, fun t u v hu hv' => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [VVRank.sv_of_isTwistPull A hv' (𝟙 _) y hJ, VVRank.sv_of_isTwistPull A hu _ y hJ, hv _ _ y J hJ, val_mul hJ,
    val_pull hJ, Units.val_mul, _root_.mul_assoc, Over.comp_left _ _ _ ψ ψ', Category.assoc]

theorem exists_twist_id (hL : L.IsLB) (n : ℤ) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t : LB.Sec (LPow A L n T), IsTwistPull A L (𝟙 _) (𝟙 _ ≫ snd _ _) rfl n n β t t := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, Category.id_comp,
        mul_inv_cancel]
      exact Fintype.prod_empty _)
    (LB.oneGen L (Y := (T ⊗ A).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  refine ⟨β, hβ, fun t => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_one, Units.val_one, _root_.one_mul, Over.id_left, Category.comp_id]

end Twist

theorem indAt_comp_unique : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ N hN p p' p'' ψ ψ' hψ
  have hG := hL.1.globalFns
  obtain ⟨Φ, hrel, -, hrat, hequ, hadd, hone⟩ := PhiProj.phi_projective hL R I hR D F N hN
  refine ⟨fun hψ' hs => ⟨by rw [Category.assoc, hψ'.1, hψ.1], fun w₀ hw₀ => ?_⟩, fun he => ⟨hψ.1, fun w₀ hw₀ => ?_⟩,
    fun h4 hψ' => ?_, fun hy hg => ⟨Category.id_comp _, fun w₀ hw₀ => ?_⟩⟩
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨w'', hw'', hΦ⟩ := hadd p p' p'' w w' hw hw' hs
    obtain ⟨β, hβ, hc⟩ := exists_twist_comp A.isLB ψ ψ' (N : ℤ) α α' hα hα'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w'', hβ, hw'', fun t t' s s' ht ht' H => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα' t
    obtain ⟨v, hv⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα u
    obtain rfl : v = t' := twist_unique A.isLB (hc t u v hu hv) H
    have e₁ := ((hrel p' w' hw').2 _ _).1 (h' t u s _ ht ((he u _).2 rfl) hu)
    have e₂ := ((hrel p w hw).2 _ _).1 (h u v _ s' ((he u _).2 rfl) ht' hv)
    refine ((hrel p'' w'' hw'').2 _ _).2 ?_
    rw [hΦ, LinearMap.comp_apply, ← e₁, e₂]
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨w', hw', hΦ⟩ := hequ p p' w hw he
    refine ⟨α, w', hα, hw', fun t t' s s' ht ht' H => ((hrel p' w' hw').2 _ _).2 ?_⟩
    rw [hΦ]
    exact ((hrel p w hw).2 _ _).1 (h t t' s s' ht ht' H)
  · obtain ⟨w₀, hw₀⟩ := U.ext
    obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨c, hc, hΦ⟩ := hrat p w w' hw hw'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine AutUniq.endo_eq_of_sections hL R A F N h4 ψ ψ' hψ.1 hψ'.1 α α' hα hα'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc)) fun t t₁ t₂ h₁ h₂ j => ?_
    have e₁ := ((hrel p w hw).2 _ _).1 (h t t₁ _ _ ((he t _).2 rfl) ((he t₁ _).2 rfl) h₁)
    have e₂ := ((hrel p w' hw').2 _ _).1 (h' t t₂ _ _ ((he t _).2 rfl) ((he t₂ _).2 rfl) h₂)
    rw [hΦ, LinearMap.smul_apply, ← e₁] at e₂
    exact congrArg (fun x => LB.Sec.f x j) (e.injective (e₂.trans (e.map_smul c t₁).symm))
  · obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F N p'.g).2.1 hg.1
    obtain ⟨β, hβ, hc⟩ := exists_twist_id (T := TFK (R := R) F) A.isLB (N : ℤ)
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w, hβ, hw.1, fun t t' s s' ht ht' H => ((hrel p' w hw.1).2 _ _).2 ?_⟩
    obtain rfl : t = t' := twist_unique A.isLB (hc t) H
    rw [hone p' w hy hg hw]
    exact ((he _ _).1 ht').symm.trans ((he _ _).1 ht)

end GlobalTheory.UT.IndComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem quasiCompact_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : Scheme.{0}} (f : X ⟶ Sp V)
    (h₁ : QuasiCompact (pullback.snd f (spMap (IsLocalRing.residue V))))
    (h₂ : QuasiCompact (pullback.snd f (jK V))) : QuasiCompact f := by
  have c₁ : CompactSpace ↥(pullback f (spMap (IsLocalRing.residue V))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have c₂ : CompactSpace ↥(pullback f (jK V)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have hu : Set.range (pullback.fst f (spMap (IsLocalRing.residue V))) ∪ Set.range (pullback.fst f (jK V)) =
      Set.univ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro x
    have hx : (Sp V).fromSpecResidueField (f x) (default : PrimeSpectrum _) = f x :=
      Scheme.fromSpecResidueField_apply _ _
    rcases ZJ.field_point_factor_dvr V ((Sp V).residueField (f x)) ((Sp V).fromSpecResidueField (f x)) with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
    · exact Or.inr ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
  have : CompactSpace X := ⟨hu ▸ (isCompact_range (pullback.fst f _).continuous).union
    (isCompact_range (pullback.fst f _).continuous)⟩
  exact (quasiCompact_iff_compactSpace f).2 this

theorem isSemiAbelian_of_unifPre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  intro V _ _ _ D A G _ _ U
  obtain ⟨E, -, -, -, -, hE⟩ := gtCoord_isGt V (maximalIdeal V) D.toPre 0 G ⟨U.gt 0⟩
  have h0 := isSemiAbelian_of_isGt _ E _ hE
  have := U.gen_hom
  have hK : IsSemiAbelian ((Over.pullback (jK V)).obj G) :=
    isSemiAbelian_of_grpIso U.gen (isSemiAbelian_of_isAbelianScheme A.A A.isAb)
  let ρ : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V :=
    Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num))
  have hr : spMap (residue V) = spMap ρ ≫ thick V (maximalIdeal V) 0 := by
    rw [← Spec.map_comp]
    congr 1
  have hk : IsSemiAbelian ((Over.pullback (spMap (residue V))).obj G) := by
    rw [hr]
    exact isSemiAbelian_of_grpIso (pullCompIso (spMap ρ) (thick V (maximalIdeal V) 0) G)
      (IsSemiAbelian.pullback (spMap ρ) _ h0)
  exact ZJ.isSemiAbelian_of_fibres_dvr V G U.smooth U.separated
    (quasiCompact_of_fibres_dvr V G.hom hk.quasiCompact hK.quasiCompact) hk hK

end GlobalTheory
end

