import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0006
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0003

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbTransfer
section
noncomputable section

open GlobalTheory.BCT

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem avg_const_frobenius_local_pairs {A : Type} [Group A] (c : ℂ) : avg (fun _ : A => c) = c := by
  have hS : rStab (fun _ : A => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [hS, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  haveI : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
  exact finsum_eq_single (fun _ : A ⧸ (⊤ : Subgroup A) => c) 1
    (fun q hq => absurd (Subsingleton.elim q 1) hq)

private theorem conj_self {G : Type} [Group G] (S : Subgroup G) {s : G} (hs : s ∈ S) :
    S.map (MulAut.conj s).toMonoidHom = S := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact S.mul_mem (S.mul_mem hs hz) (S.inv_mem hs)
  · intro hy
    exact ⟨s⁻¹ * y * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hy) hs, by group⟩

private theorem zpowers_closed {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (t : H) :
    IsCompact (closure (Subgroup.zpowers (j t) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set H)) := by
  have hz : (Subgroup.zpowers (j t) : Set G) = j '' (Subgroup.zpowers t : Set H) := by
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
  rw [hz, hj.closure_image_eq, hj.isInducing.isCompact_iff]

private theorem cpt_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (T : Subgroup H) :
    cptPart (T.map j) = (cptPart T).map j := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (zpowers_closed j hj t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (zpowers_closed j hj t).2 hc⟩

private theorem conj_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) :
    Topology.IsClosedEmbedding (MulAut.conj c).toMonoidHom := by
  have h : ((MulAut.conj c).toMonoidHom : G → G) = (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹) := by
    ext x
    simp [MulAut.conj_apply]
  rw [h]
  exact Homeomorph.isClosedEmbedding _

private def wt {G : Type} [Group G] [TopologicalSpace G] (T K : Subgroup G) (x : G) : ℕ :=
  (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T)

private theorem wt_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G)
    {t κ : G} (ht : t ∈ T) (hκ : κ ∈ K) (x : G) : wt T K (t * x * κ) = wt T K x := by
  unfold wt
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hT : T.map (MulAut.conj t).toMonoidHom = T := conj_self T ht
  have hKm : K.map (MulAut.conj (t * x * κ)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨x * (κ * k * κ⁻¹) * x⁻¹,
        ⟨κ * k * κ⁻¹, K.mul_mem (K.mul_mem hκ hk) (K.inv_mem hκ), rfl⟩, by group⟩
    · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨κ⁻¹ * k * κ, K.mul_mem (K.mul_mem (K.inv_mem hκ) hk) hκ, by group⟩
  have hcpt : (cptPart T).map (MulAut.conj t).toMonoidHom = cptPart T := by
    rw [← cpt_map _ (conj_closed t) T, hT]
  have hI : T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, hT]
  rw [hKm]
  calc (T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).relIndex (cptPart T)
      = ((T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).relIndex
          ((cptPart T).map (MulAut.conj t).toMonoidHom) := by rw [hI, hcpt]
    _ = _ := Subgroup.relIndex_map_map_of_injective _ _ hinj

private theorem wt_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (T₀ : Subgroup H) (K : Subgroup G) (K₀ : Subgroup H)
    (hK : ∀ h, j h ∈ K ↔ h ∈ K₀) (h : H) : wt (T₀.map j) K (j h) = wt T₀ K₀ h := by
  unfold wt
  have h2 : T₀.map j ⊓ K.map (MulAut.conj (j h)).toMonoidHom =
      (T₀ ⊓ K₀.map (MulAut.conj h).toMonoidHom).map j := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, k, hk, hkt⟩
      refine ⟨t, ⟨ht, h⁻¹ * t * h, (hK _).1 ?_, by group⟩, rfl⟩
      have : k = j (h⁻¹ * t * h) := by
        simp only [map_mul, map_inv, ← hkt]
        group
      exact this ▸ hk
    · rintro ⟨t, ⟨ht, k, hk, rfl⟩, rfl⟩
      exact ⟨⟨_, ht, rfl⟩, j k, (hK k).2 hk, by simp⟩
  rw [h2, cpt_map j hj]
  exact Subgroup.relIndex_map_map_of_injective _ _ hj.injective

private theorem sum_transfer {G H : Type} [Group G] [Group H] (j : H →* G) (hj : Function.Injective j)
    (T : Subgroup G) (T₀ : Subgroup H) (hT : T = T₀.map j) (K : Subgroup G) (K₀ : Subgroup H)
    (hK : ∀ h, j h ∈ K ↔ h ∈ K₀) (F : G → ℂ) (F₀ : H → ℂ)
    (hinv : ∀ t ∈ T, ∀ κ ∈ K, ∀ x, F (t * x * κ) = F x) (hjF : ∀ h, F (j h) = F₀ h)
    (hsupp : ∀ x, F x ≠ 0 → ∃ h, ∃ κ ∈ K, x = j h * κ) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), F (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H), F₀ (Quotient.out q) := by
  classical
  subst hT
  let e : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H) →
      DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) :=
    fun p => DoubleCoset.mk (T₀.map j) K (j (Quotient.out p))
  have hval : ∀ x, F (Quotient.out (DoubleCoset.mk (T₀.map j) K x)) = F x := by
    intro x
    obtain ⟨a, b, ha, hb, hx⟩ := DoubleCoset.mk_out_eq_mul (T₀.map j) K x
    rw [hx]
    exact hinv a ha b hb x
  have he' : ∀ h, e (DoubleCoset.mk T₀ K₀ h) = DoubleCoset.mk (T₀.map j) K (j h) := by
    intro h
    obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T₀ K₀ h
    show DoubleCoset.mk (T₀.map j) K (j (Quotient.out (DoubleCoset.mk T₀ K₀ h))) = _
    rw [hab, DoubleCoset.eq]
    refine ⟨(j a)⁻¹, (T₀.map j).inv_mem (Subgroup.mem_map_of_mem j ha), (j b)⁻¹,
      K.inv_mem ((hK b).mpr hb), ?_⟩
    simp only [map_mul]
    group
  have he : Function.Injective e := by
    intro p p' hpp
    have hpp' : DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)) =
        DoubleCoset.mk (T₀.map j) K (j (Quotient.out p')) := hpp
    rw [DoubleCoset.eq] at hpp'
    obtain ⟨a, ha, b, hb, hab⟩ := hpp'
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← DoubleCoset.out_eq' T₀ K₀ p, ← DoubleCoset.out_eq' T₀ K₀ p', DoubleCoset.eq]
    have hjb : j ((a₀ * Quotient.out p)⁻¹ * Quotient.out p') = b := by
      rw [map_mul, map_inv, map_mul, hab]
      group
    refine ⟨a₀, ha₀, (a₀ * Quotient.out p)⁻¹ * Quotient.out p', ?_, by group⟩
    rw [← hK, hjb]
    exact hb
  have hsub : Function.support
      (fun q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) =>
        F (Quotient.out q)) ⊆ Set.range e := by
    intro q hq
    obtain ⟨h, κ, hκ, hx⟩ := hsupp _ hq
    refine ⟨DoubleCoset.mk T₀ K₀ h, ?_⟩
    rw [he', ← DoubleCoset.out_eq' (T₀.map j) K q, DoubleCoset.eq]
    exact ⟨1, (T₀.map j).one_mem, κ, hκ, by rw [hx, one_mul]⟩
  have hfull : ∑ᶠ q ∈ Set.range e, F (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G),
        F (Quotient.out q) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsub]
  rw [← hfull, finsum_mem_range he]
  refine finsum_congr (fun p => ?_)
  show F (Quotient.out (DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)))) = F₀ (Quotient.out p)
  rw [hval, hjF]

theorem orbTransfer : OrbTransfer := by
  intro G H _ _ _ _ _ _ _ _ j hj θ K K₀ hK δ γ hT φ f hφ hsupp hφf hθ
  have hconst : ∀ x : G, (avg fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = φ (x⁻¹ * δ * θ x) := by
    intro x
    have e : (fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = fun _ => φ (x⁻¹ * δ * θ x) := by
      funext k
      rw [← hφ (k : G) k.2 (x⁻¹ * δ * θ x)]
      congr 1
      rw [map_mul]
      group
    rw [e, avg_const_frobenius_local_pairs]
  have hconst₀ : ∀ y : H, (avg fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) =
      f (y⁻¹ * γ * y) := by
    intro y
    have e : (fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) = fun _ => f (y⁻¹ * γ * y) := by
      funext k
      rw [MonoidHom.id_apply, ← hφf, ← hφf, ← hφ (j k) ((hK k).2 k.2) ((j y)⁻¹ * δ * θ (j y))]
      congr 1
      rw [map_mul, map_mul]
      group
    rw [e, avg_const_frobenius_local_pairs]
  have hinv : ∀ t ∈ twCent θ δ, ∀ κ ∈ K, ∀ x : G,
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (t * x * κ) =
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x := by
    intro t ht κ hκ x
    have ht' : t * δ = δ * θ t := ht
    have e : (t * x * κ)⁻¹ * δ * θ (t * x * κ) = κ⁻¹ * (x⁻¹ * δ * θ x) * θ κ := by
      rw [map_mul, map_mul]
      calc (t * x * κ)⁻¹ * δ * (θ t * θ x * θ κ)
          = κ⁻¹ * x⁻¹ * t⁻¹ * (δ * θ t) * θ x * θ κ := by group
        _ = _ := by rw [← ht']; group
    simp only
    rw [wt_inv (twCent θ δ) K ht hκ x, e, hφ κ hκ]
  have hjF : ∀ y : H,
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (j y) =
      (fun y => (wt (twCent (MonoidHom.id H) γ) K₀ y : ℂ) * f (y⁻¹ * γ * y)) y := by
    intro y
    simp only
    rw [hT, wt_map j hj _ K K₀ hK y, hφf]
  have hsupp' : ∀ x : G, (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x ≠ 0 →
      ∃ y, ∃ κ ∈ K, x = j y * κ := by
    intro x hx
    apply hsupp x
    intro h0
    apply hx
    simp only [h0, mul_zero]
  unfold twOrb
  simp only [hconst, hconst₀]
  exact sum_transfer j hj.injective (twCent θ δ) (twCent (MonoidHom.id H) γ) hT K K₀ hK _ _
    hinv hjF hsupp'

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRad
section
open ValuativeRel Matrix Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_rad {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ r < γ := by
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hc0 : 0 < valuation k x := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)
  have hm0 : 0 < min γ 1 := lt_min (zero_lt_iff.2 hγ) zero_lt_one
  have hlt : valuation k x * min γ 1 < min γ 1 := mul_lt_of_lt_one_left hm0 hx1
  exact ⟨valuation k x * min γ 1, mul_pos hc0 hm0, hlt.trans_le (min_le_right _ _), hlt.trans_le (min_le_left _ _)⟩

private theorem nhds_rad {x : k} {W : Set k} (hW : W ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | valuation k (y - x) ≤ r} ⊆ W := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds' x).mem_iff.1 hW
  obtain ⟨r, h0, h1, h2⟩ := exists_rad hγ
  exact ⟨r, h0, h1, fun y hy => hs (lt_of_le_of_lt hy h2)⟩

private theorem fin_rad {ι : Type} [Finite ι] (R : ι → ValueGroupWithZero k) (h0 : ∀ i, 0 < R i) (h1 : ∀ i, R i < 1) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ i, r ≤ R i := by
  obtain ⟨c, hc0, hc1, -⟩ := exists_rad (k := k) one_ne_zero
  obtain ⟨o, ho⟩ := Finite.exists_min (fun o : Option ι => o.elim c R)
  refine ⟨o.elim c R, ?_, ?_, fun i => ho (some i)⟩
  · cases o with
    | none => exact hc0
    | some i => exact h0 i
  · cases o with
    | none => exact hc1
    | some i => exact h1 i

private theorem pi_rad {ι : Type} [Finite ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (P : ∀ i, ValueGroupWithZero k → Set (X i))
    (hP : ∀ i, ∀ W ∈ 𝓝 (x i), ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ P i r ⊆ W)
    (hm : ∀ i r r', r' ≤ r → P i r' ⊆ P i r) {V : Set (∀ i, X i)} (hV : V ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | ∀ i, y i ∈ P i r} ⊆ V := by
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hsub⟩ := hV
  choose R h0 h1 hR using fun i => hP i (t i) (ht i)
  obtain ⟨r, hr0, hr1, hr⟩ := fin_rad R h0 h1
  exact ⟨r, hr0, hr1, fun y hy => hsub fun i _ => hR i (hm i _ _ (hr i) (hy i))⟩

private theorem mat_rad {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)} (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧
      {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r} ⊆ V := by
  refine pi_rad (X := fun _ : Fin n => Fin n → k) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun i r => {y | ∀ j, valuation k (y j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun i W hW => ?_)
    (fun i r r' h y hy j => (hy j).trans h) hV
  exact pi_rad (X := fun _ : Fin n => k) (fun j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun j r => {y | valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun j W hW => nhds_rad hW)
    (fun j r r' h y hy => (show valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r from le_trans hy h)) hW

private theorem unit_nhds {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∃ V ∈ 𝓝 (1 : A), ∀ g : Aˣ, (g : A) ∈ V → ((g⁻¹ : Aˣ) : A) ∈ V → g ∈ U := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.1 (by simpa using hT)
  refine ⟨a ∩ MulOpposite.op ⁻¹' b, Filter.inter_mem ha
    (MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hb)), fun g h1 h2 => hTU ?_⟩
  exact hab ⟨h1.1, h2.2⟩

private theorem val_near {r : ValueGroupWithZero k} (h1 : r < 1) {x : k} (hx : valuation k (x - 1) ≤ r) :
    valuation k x = 1 := by
  have h := Valuation.map_one_add_of_lt (valuation k) (lt_of_le_of_lt hx h1)
  simpa using h

private theorem near_mul' {r : ValueGroupWithZero k} (h1 : r < 1) {x y : k} (hx : valuation k (x - 1) ≤ r)
    (hy : valuation k (y - 1) ≤ r) : valuation k (x * y - 1) ≤ r := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul, val_near h1 hx, one_mul]
  exact hy

private theorem near_inv' {r : ValueGroupWithZero k} (h1 : r < 1) (x : kˣ) (hx : valuation k ((x : k) - 1) ≤ r) :
    valuation k (((x⁻¹ : kˣ) : k) - 1) ≤ r := by
  have hv := val_near h1 hx
  have e : ((x⁻¹ : kˣ) : k) - 1 = -((x : k) - 1) * ((x⁻¹ : kˣ) : k) := by
    rw [neg_mul, sub_mul, Units.mul_inv]
    ring
  have hv' : valuation k ((x⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  rw [e, map_mul, hv', mul_one, Valuation.map_neg]
  exact hx

private theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

private theorem compact_units (r : ValueGroupWithZero k) (h1 : r < 1) :
    IsCompact {x : kˣ | valuation k ((x : k) - 1) ≤ r} := by
  haveI : T2Space k := t2
  have hC : IsCompact {x : k | valuation k (x - 1) ≤ r} := by
    have h := (IsNonarchimedeanLocalField.isCompact_closedBall k r).image (f := fun x => x + 1) (by fun_prop)
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨x - 1, hx, sub_add_cancel _ _⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have h := (Units.isClosedEmbedding_embedProduct (α := k)).isCompact_preimage
    (hC.prod (hC.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    MulOpposite.op_injective.mem_set_image]
  exact ⟨fun hx => ⟨hx, near_inv' h1 x hx⟩, fun hx => hx.1⟩

end SlopeTestRemainingChoices

theorem smallRad :
    UpperTheory.Gal.InertialTypesAlt.L.SmallRad := by
  intro k _ _ _ _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨V, hV, hVU⟩ := unit_nhds hU
    obtain ⟨r, h0, h1, hr⟩ := mat_rad hV
    obtain ⟨K, hK, -, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1
    refine ⟨r, h0, h1, fun r' hr' g hg => ?_⟩
    have hg' : g ∈ ball n r := fun i j => (hg i j).trans hr'
    have hgK : g ∈ K := by
      have : g ∈ (K : Set (GL (Fin n) k)) := hK ▸ hg'
      exact this
    have hinv : g⁻¹ ∈ ball n r := by
      have : g⁻¹ ∈ (K : Set (GL (Fin n) k)) := K.inv_mem hgK
      exact hK ▸ this
    exact hVU g (hr hg') (hr hinv)
  · intro W hW
    obtain ⟨r, h0, h1, hr⟩ := pi_rad (X := fun _ : Fin n => kˣ) (1 : Fin n → kˣ)
      (fun _ r => {u : kˣ | valuation k ((u : k) - 1) ≤ r}) (fun i Y hY => by
        obtain ⟨V, hV, hVU⟩ := unit_nhds hY
        obtain ⟨r, h0, h1, hr⟩ := nhds_rad hV
        exact ⟨r, h0, h1, fun u hu => hVU u (hr hu) (hr (near_inv' h1 u hu))⟩)
      (fun _ r r' h y hy => (show valuation k ((y : k) - 1) ≤ r from le_trans hy h)) hW
    exact ⟨r, h0, h1, fun r' hr' u hu => hr fun i => (hu i).trans hr'⟩
  · intro r h1
    refine ⟨{ carrier := {u | Near r u}
              one_mem' := fun i => by simp
              mul_mem' := fun {a b} ha hb i => by
                simpa using near_mul' h1 (ha i) (hb i)
              inv_mem' := fun {a} ha i => by
                simpa using near_inv' h1 (a i) (ha i) }, fun u => Iff.rfl, ?_⟩
    have h := isCompact_univ_pi (fun _ : Fin n => compact_units r h1)
    convert h using 1
    ext u
    simp [Near, Set.mem_pi]
  · exact (continuous_leviEmb k (points (Fin n))).comp (continuous_leviTorus k (Fin n))
  · obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    refine ⟨fun i => Units.mk0 x hx0 ^ (n - (i : ℕ)), fun i j hij => ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    have hij' : (i : ℕ) < j := hij
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)) hx1 (by omega)
  · intro t₀ t h₀ ht i j hij
    have a := h₀ i j hij
    have b := ht i j hij
    have c : 0 < valuation k (t j : k) := zero_lt_iff.2 (by simp)
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    calc valuation k (t₀ i : k) * valuation k (t i : k) ≤ valuation k (t₀ i : k) * valuation k (t j : k) :=
          mul_le_mul_right b _
      _ < valuation k (t₀ j : k) * valuation k (t j : k) := mul_lt_mul_of_pos_right a c

end UpperTheory.Gal.InertialTypesAlt.L
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictMap
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori

private theorem map_diag {E F : Type} [Field E] [Field F] {n : ℕ} (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [val_diagT]
  · simp [val_diagT, Matrix.diagonal_apply, hij]

private theorem diag_comm {E : Type} [Field E] {n : ℕ} (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

private theorem strict_map {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] {n : ℕ} {t : Fin n → kˣ} (ht : Strict t) :
    Strict fun i => Units.map (algebraMap k E : k →* E) (t i) := by
  intro i j hij
  have h := ht i j hij
  rw [← (valuation k).vlt_iff_lt] at h
  rw [← (valuation E).vlt_iff_lt]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  intro hle
  exact h ((ValuativeExtension.vle_iff_vle _ _).mp hle)

theorem UpperTheory.Gal.InertialTypesAlt.L.align :
    UpperTheory.Gal.InertialTypesAlt.L.Align := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n δ h y γ d hd hnorm hy
  obtain ⟨hcyc, -, hb⟩ := bridge k E σ
  obtain ⟨hsg, hnrm, -, -, -⟩ := hb n
  obtain ⟨hND, -, -⟩ := normDiag k E σ hσ n
  obtain ⟨hN, hstr, hreg⟩ := hND d
  have e := nrm_conj hcyc.ord δ y
  rw [hsg y, hy, hnrm, hnrm, hN, hnorm] at e
  set T := diagT k (Fin n) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d) with hTdef
  obtain ⟨z, hz⟩ := conjDesc k E n T γ (hreg hd) ⟨h⁻¹ * y, by rw [e]; group⟩
  refine ⟨z, by rw [hz]; group, ?_⟩
  intro t ht
  have hct : γ * t = t * γ := Subgroup.mem_centralizer_iff.mp ht γ rfl
  set m : Fin n → Eˣ := fun i => Units.map (algebraMap k E : k →* E) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d i) with hm
  have hms : Strict m := strict_map (hstr hd)
  have hT : (incl T : GL (Fin n) E) = diagT E (Fin n) m := map_diag (algebraMap k E) _
  have hrefl : Cyc (RingEquiv.refl E) 1 := ⟨fun x => rfl, one_pos, fun x => rfl⟩
  have hsgr : ∀ g : GL (Fin n) E, sg (RingEquiv.refl E) g = g := by
    intro g
    ext i j
    rfl
  set u := z⁻¹ * t * z with hu
  have huc : u * T = T * u := by
    have hz' : T = z⁻¹ * γ * z := by rw [hz]; group
    rw [hz', hu]
    calc z⁻¹ * t * z * (z⁻¹ * γ * z) = z⁻¹ * (t * γ) * z := by group
      _ = z⁻¹ * (γ * t) * z := by rw [hct]
      _ = z⁻¹ * γ * z * (z⁻¹ * t * z) := by group
  obtain ⟨s2, hs2⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms (incl u) (by
    rw [hsgr, ← hT, ← map_inv, ← map_mul, ← map_mul, mul_assoc, ← huc]
    congr 1
    group)
  set w := y⁻¹ * h * incl z with hw
  have hg : (incl γ : GL (Fin n) E) = incl z * incl T * (incl z)⁻¹ := by
    rw [hz]
    simp only [map_mul, map_inv]
  have hwc0 : (incl T : GL (Fin n) E) = w * incl T * w⁻¹ := by
    conv_lhs => rw [e]
    rw [hg, hw]
    group
  have hwc : w⁻¹ * diagT E (Fin n) m * w = diagT E (Fin n) m := by
    rw [← hT]
    conv_lhs => rw [hwc0]
    group
  obtain ⟨s1, hs1⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms w (by rw [hsgr]; exact hwc)
  have ht' : (incl t : GL (Fin n) E) = incl z * incl u * (incl z)⁻¹ := by
    rw [hu]
    simp only [map_mul, map_inv]
    group
  have key : y⁻¹ * (h * incl t * h⁻¹) * y = w * incl u * w⁻¹ := by
    rw [ht', hw]
    group
  rw [key, hs1, hs2, diag_comm]
  group
end

