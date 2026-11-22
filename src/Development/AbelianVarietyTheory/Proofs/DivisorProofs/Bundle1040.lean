import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfLe
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClsInt

section Count
variable {H Γ : Type} [Group H] [Group Γ] (ι : Γ →* H) (J J' : Subgroup H)

def toLev (a : H) : Bridge.stab ι J a →* J where
  toFun s := ⟨a⁻¹ * ι s * a, (Bridge.mem_stab _).1 s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem sum_inv_card_stab (hle : J' ≤ J) (hN : J'.relIndex J ≠ 0) {Cl : Type} [Fintype Cl] (y : Cl → H)
    (hy : Bridge.IsReps ι J' y) (a : H) [Finite (Bridge.stab ι J a)] :
    ∑ k with (∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J' (y k)) : ℕ) : ℂ)⁻¹ =
      ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ)⁻¹ := by
  let X := J ⧸ J'.subgroupOf J
  have hX : Nat.card X = J'.relIndex J := rfl
  haveI : Finite X := Nat.finite_of_card_ne_zero (hX ▸ hN)
  letI : Fintype X := Fintype.ofFinite X
  letI : MulAction (Bridge.stab ι J a) X := MulAction.compHom X (toLev ι J a)
  have hsm : ∀ (s : Bridge.stab ι J a) (u : J), s • (u : X) = ((toLev ι J a s * u : J) : X) := fun _ _ => rfl
  choose idx hidx hu using fun h => (hy h)
  have hi : ∀ h k, idx h = k ↔ ∃ γ, ∃ w ∈ J', h = ι γ * y k * w := by
    intro h k
    constructor
    · rintro rfl
      obtain ⟨γ, w, e⟩ := hidx h
      exact ⟨γ, w, w.2, e⟩
    · rintro ⟨γ, w, hw, e⟩
      exact (hu h k ⟨γ, ⟨w, hw⟩, e⟩).symm
  let f : X → Cl := fun x => idx (a * (x.out : J))
  have hq : ∀ u v : J, (u : X) = (v : X) ↔ (u : H)⁻¹ * v ∈ J' := fun u v => QuotientGroup.eq
  have hf : ∀ (u : J) k, f (u : X) = k ↔ ∃ γ, ∃ w ∈ J', a * u = ι γ * y k * w := by
    intro u k
    have h0 : ((Quotient.out (u : X) : J) : H)⁻¹ * u ∈ J' := (hq _ _).1 (Quotient.out_eq _)
    change idx _ = k ↔ _
    rw [hi]
    constructor
    · rintro ⟨γ, w, hw, e⟩
      exact ⟨γ, _, J'.mul_mem hw h0, by rw [← mul_assoc, ← e]; group⟩
    · rintro ⟨γ, w, hw, e⟩
      exact ⟨γ, _, J'.mul_mem hw (J'.inv_mem h0), by rw [← mul_assoc, ← e]; group⟩
  have hS : ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hN' : ((J'.relIndex J : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hcount : J'.relIndex J = ∑ k with (∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      (Finset.univ.filter fun x => f x = k).card := by
    rw [← hX, Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_eq_sum_card_fiberwise fun x _ => ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨γ, w, hw, e⟩ := (hf u _).1 rfl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨γ⁻¹, u * w⁻¹, J.mul_mem u.2 (J.inv_mem (hle hw)), ?_⟩
    rw [map_inv, mul_assoc, ← mul_assoc a, e]; group
  have key : ∀ k, (∃ γ, ∃ u ∈ J, y k = ι γ * a * u) →
      (Finset.univ.filter fun x => f x = k).card * Nat.card (Bridge.stab ι J' (y k)) =
        Nat.card (Bridge.stab ι J a) := by
    rintro k ⟨γ₀, u₀, hu₀, e₀⟩
    let x₀ : X := ((⟨u₀, hu₀⟩ : J) : X)
    have h1 : MulAction.orbit (Bridge.stab ι J a) x₀ = ↑(Finset.univ.filter fun x => f x = k) := by
      ext x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hf, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨s, hs⟩
        rw [hsm, hq] at hs
        refine ⟨s * γ₀⁻¹, _, hs, ?_⟩
        change _ = _ * ((a⁻¹ * ι s * a * u₀)⁻¹ * u)
        rw [e₀, map_mul, map_inv]; group
      · rintro ⟨γ, w, hw, e⟩
        have e1 : a⁻¹ * ι (γ * γ₀) * a = u * w⁻¹ * u₀⁻¹ := by
          have : (u : H) = a⁻¹ * (ι γ * y k * w) := by rw [← e]; group
          rw [this, e₀, map_mul]; group
        refine ⟨⟨γ * γ₀, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
        · rw [e1]; exact J.mul_mem (J.mul_mem u.2 (J.inv_mem (hle hw))) (J.inv_mem hu₀)
        · rw [hsm, hq]
          change (a⁻¹ * ι (γ * γ₀) * a * u₀)⁻¹ * u ∈ J'
          rw [e1, show ((u : H) * w⁻¹ * u₀⁻¹ * u₀)⁻¹ * u = w by group]
          exact hw
    have h2 : ∀ s : Bridge.stab ι J a, s ∈ MulAction.stabilizer (Bridge.stab ι J a) x₀ ↔
        γ₀ * s * γ₀⁻¹ ∈ Bridge.stab ι J' (y k) := by
      intro s
      rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, hq, Bridge.mem_stab]
      change u₀⁻¹ * (a⁻¹ * ι s * a * u₀) ∈ J' ↔ _
      rw [e₀, map_mul, map_mul, map_inv, show (ι γ₀ * a * u₀)⁻¹ * (ι γ₀ * ι s * (ι γ₀)⁻¹) * (ι γ₀ * a * u₀) =
        u₀⁻¹ * (a⁻¹ * ι s * a * u₀) by group]
    have h3 : Nat.card (MulAction.stabilizer (Bridge.stab ι J a) x₀) = Nat.card (Bridge.stab ι J' (y k)) := by
      refine Nat.card_eq_of_bijective (fun s => ⟨γ₀ * s.1 * γ₀⁻¹, (h2 _).1 s.2⟩) ⟨fun s t e => ?_, fun t => ?_⟩
      · have := congrArg Subtype.val e
        simp only [mul_left_inj, mul_right_inj] at this
        exact Subtype.ext (Subtype.ext this)
      · have ht := (Bridge.mem_stab _).1 t.2
        have hm : γ₀⁻¹ * t * γ₀ ∈ Bridge.stab ι J a := by
          rw [Bridge.mem_stab, map_mul, map_mul, map_inv,
            show a⁻¹ * ((ι γ₀)⁻¹ * ι t * ι γ₀) * a = u₀ * ((ι γ₀ * a * u₀)⁻¹ * ι t * (ι γ₀ * a * u₀)) * u₀⁻¹ by group,
            ← e₀]
          exact J.mul_mem (J.mul_mem hu₀ (hle ht)) (J.inv_mem hu₀)
        have e : γ₀ * (γ₀⁻¹ * t * γ₀) * γ₀⁻¹ = t := by group
        exact ⟨⟨⟨_, hm⟩, (h2 _).2 (by rw [e]; exact t.2)⟩, Subtype.ext e⟩
    rw [← h3, ← Set.ncard_coe_finset, ← h1, ← Nat.card_coe_set_eq, ← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ x₀)
  have h4 : ∀ k ∈ Finset.univ.filter (fun k => ∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J' (y k)) : ℕ) : ℂ)⁻¹ =
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ)⁻¹ *
        (((Finset.univ.filter fun x => f x = k).card : ℕ) : ℂ) := by
    intro k hk
    have h5 := key k (Finset.mem_filter.1 hk).2
    have h6 := hS
    rw [← h5] at h6 ⊢
    push_cast at h6 ⊢
    have h7 := left_ne_zero_of_mul h6
    have h8 := right_ne_zero_of_mul h6
    field_simp
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Nat.cast_sum, ← hcount]
  field_simp

end Count

theorem integral_eq_sum_of_le {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J J' : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (hle : J' ≤ J) (hN : J'.relIndex J ≠ 0)
    (Cl : Type) [Fintype Cl] (h : Cl → G) (hy : Bridge.IsReps (π.comp Γ.subtype) J' fun k => π (h k))
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (hr : ∀ u, π u ∈ J → ∀ x, Φ (x * u) = Φ x) :
    ∫ x in 𝓖, Φ x ∂ν = ∑ k, ((J'.relIndex J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (π.comp Γ.subtype) J' (π (h k))) : ℕ) : ℂ)⁻¹ * Φ (h k) := by
  set ι := π.comp Γ.subtype with hι
  choose σ hσ using hπ
  have hΦ : ∀ x, Φ (σ (π x)) = Φ x := fun x => by
    rw [← hr ((σ (π x))⁻¹ * x) (by rw [map_mul, map_inv, hσ, inv_mul_cancel]; exact J.one_mem),
      mul_inv_cancel_left]
  have hΦ' : ∀ (γ : Γ) z (k : J), Φ (σ (ι γ * z * k)) = Φ (σ z) := fun γ z k => by
    have : ι γ * z * k = π (γ * σ z * σ k) := by rw [map_mul, map_mul, hσ, hσ]; rfl
    rw [this, hΦ, hr _ (by rw [hσ]; exact k.2), hl _ γ.2]
  have hfin : ∀ z, Finite (Bridge.stab ι J z) := fun z => by
    have := GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ (J.comap π) h𝓖 (h1 ▸ one_ne_zero)
      (h1 ▸ ENNReal.one_ne_top) (σ z)
    refine Set.Finite.subset this fun γ hγ => ?_
    rw [Set.mem_setOf_eq, Subgroup.mem_comap, map_mul, map_mul, map_inv, hσ]
    exact (Bridge.mem_stab _).1 hγ
  let r : Setoid Cl :=
    { r := fun k l => ∃ γ, ∃ u ∈ J, π (h k) = ι γ * π (h l) * u
      iseqv :=
        ⟨fun k => ⟨1, 1, J.one_mem, by simp⟩,
          fun ⟨γ, u, hu, e⟩ => ⟨γ⁻¹, u⁻¹, J.inv_mem hu, by rw [e, map_inv]; group⟩,
          fun ⟨γ, u, hu, e⟩ ⟨δ, v, hv, e'⟩ => ⟨γ * δ, v * u, J.mul_mem hv hu, by rw [e, e', map_mul]; group⟩⟩ }
  have hq : ∀ k (i : Quotient r), Quotient.mk r k = i ↔ ∃ γ, ∃ u ∈ J, π (h k) = ι γ * π (h i.out) * u :=
    fun k i => Quotient.mk_eq_iff_out
  have hreps : Bridge.IsReps ι J fun i : Quotient r => π (h i.out) := by
    intro z
    obtain ⟨k, ⟨γ, w, e⟩, -⟩ := hy z
    refine ⟨Quotient.mk r k, ?_, ?_⟩
    · obtain ⟨δ, u, hu, e'⟩ := (hq k _).1 rfl
      exact ⟨γ * δ, ⟨u * w, J.mul_mem hu (hle w.2)⟩, by simp only [] at e ⊢; rw [e, e', map_mul]; group⟩
    · rintro i ⟨δ, u, e'⟩
      refine ((hq k i).2 ⟨γ⁻¹ * δ, u * (w : H)⁻¹, J.mul_mem u.2 (J.inv_mem (hle w.2)), ?_⟩).symm
      simp only [] at e e'
      have : π (h k) = (ι γ)⁻¹ * z * (w : H)⁻¹ := by rw [e]; group
      rw [this, e', map_mul, map_inv]; group
  have key := GlobalTheory.ClassUnfold.integral_eq_sum_of_surjective ν Γ π (fun z => ⟨σ z, hσ z⟩) J 𝓖 h𝓖 ho h1
    (Quotient r) _ hreps (fun _ => hfin _) (fun z => Φ (σ z)) hΦ'
  simp only [hΦ] at key
  rw [key, ← Finset.sum_fiberwise Finset.univ (Quotient.mk r)]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := hfin (π (h i.out))
  rw [← sum_inv_card_stab ι J J' hle hN _ hy, Finset.sum_mul]
  refine Finset.sum_congr (Finset.filter_congr fun k _ => (hq k i).symm) fun k hk => ?_
  obtain ⟨γ, u, hu, e⟩ := (hq k i).1 (Finset.mem_filter.1 hk).2
  rw [← hΦ (h k), e, hΦ' γ _ ⟨u, hu⟩, hΦ]

theorem integral_eq_classSum_of_le : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.IsPosDef → V.SigOK → IsMeasDef V (Formalism.L2.DIV.lev D.sp.cm V.gram β L) ν 𝓕 → (∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L)) → ∀ (J' : Subgroup (Bridge.Gf V)) (Cl : Type) [Fintype Cl] (h : Cl → GA D V), J' ≤ (levEnv V β L).J → J'.relIndex (levEnv V β L).J ≠ 0 → Bridge.IsReps (Bridge.ratF V) J' (fun k => fin V (h k)) → (∀ k, h k ∈ GfC V) → ∀ Φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ x, Φ (γ * x) = Φ x) → (∀ u : GA D V, fin V u ∈ (levEnv V β L).J → ∀ x, Φ (x * u) = Φ x) → ∫ x in 𝓕, Φ x ∂ν = ∑ k, ((J'.relIndex (levEnv V β L).J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (Bridge.ratF V) J' (fin V (h k))) : ℕ) : ℂ)⁻¹ * Φ (h k) := by
  intro D V β L ν 𝓕 _ _ hν hL J' Cl _ h hle hN hy _ Φ hl hr
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hν.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict =
      (Formalism.L2.DIV.lev D.sp.cm V.gram β L).comap (Lev.finE V) := by
    ext g
    exact (hL (Lev.finE V g)).symm
  refine integral_eq_sum_of_le ν (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J J' 𝓕 hν.2 ?_ ?_ hle hN Cl h hy Φ hl hr
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hν.1

end GlobalTheory.ClsInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlace
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_isIntV (G : HTGroup p) (v : AwayP p) :
    @IsCompact _ (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) {y | IsIntV G v y} := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  set b := basV G v
  have hc : Continuous b.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have hbox : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank ℚ G.C) ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) :=
    isCompact_univ_pi fun _ ↦ LevelExists.isCompact_intCompl v.1
  have hset : {y | IsIntV G v y} = b.equivFun.symm '' (Set.univ.pi fun _ ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) := by
    rw [LinearEquiv.image_symm_eq_preimage]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Module.Basis.equivFun_apply]
    rfl
  rw [hset]
  exact hbox.image hc

theorem isCompact_IntV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  intro p _ G v
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
  have hPc := isCompact_isIntV G v
  have hOc := LevelExists.isCompact_intCompl v.1
  set P : Set (Qv v ⊗[ℚ] G.C) := {y | IsIntV G v y}
  set O : Set (Qv v) := (v.1.adicCompletionIntegers ℚ : Set (Qv v))
  have hσ : Continuous (fun y : Qv v ⊗[ℚ] G.C ↦ (starT G.star (Qv v) y).unop) := by
    let σl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (Qv v) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Qv v) (Qv v ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (Qv v) : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let g : Gv G v → ((Qv v ⊗[ℚ] G.C) × (Qv v ⊗[ℚ] G.C)ᵐᵒᵖ) × (Qv v × (Qv v)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding g :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  let K := (P ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P)) ×ˢ (O ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' O))
  have hKC : IntV G v = g ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [hKC]
  exact hg.isCompact_preimage ((hPc.prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod
    (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlaces
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp_of_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε h₁ h₂
  classical
  haveI : FiniteDimensional F E := inferInstance
  have h₁' : ∀ w : InfinitePlace F, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ (w ∈ S₁ →
      ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g =
        JR w.Completion J → ∀ i j, g i j ∈ C) := by
    intro w
    by_cases hw : w ∈ S₁
    · obtain ⟨C, hC, hC'⟩ := h₁ w hw
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hw⟩
  have h₂' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ (v ∈ S₂ →
      ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g =
        JR (Fv F v) J → ∀ i j, g i j ∈ C) := by
    intro v
    by_cases hv : v ∈ S₂
    · obtain ⟨C, hC, hC'⟩ := h₂ v hv
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hv⟩
  choose C₁ hC₁ hC₁' using h₁'
  choose C₂ hC₂ hC₂' using h₂'
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Set (AF F ⊗[F] E)), (∀ i ∈ s, IsCompact (f i)) →
      IsCompact (∑ i ∈ s, f i) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, ← Set.singleton_zero]; exact isCompact_singleton
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  set e := algebraMap (AF F) (AF F ⊗[F] E) ε with he
  let X : Set (AF F ⊗[F] E) := (fun δ => δ * (1 - e)) '' ({0, 1} : Set (AF F ⊗[F] E)) +
    (∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) '' C₁ w) +
    ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) '' C₂ v
  have hX : IsCompact X :=
    ((((Set.toFinite _).isCompact).image (continuous_id.mul continuous_const)).add
      (hsum _ _ fun w _ => (hC₁ w).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))).add (hsum _ _ fun v _ => (hC₂ v).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))
  refine GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces σ J ε X hX (GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces σ J ε) fun g hg i j => ?_
  have hu : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := by
    let g' : HR (AF F) σ J := g
    exact g'.2
  set a := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with ha
  set δ := (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with hδ
  have hfix : e * (a - δ) = a - δ := by
    have := hg.2 i j
    simpa only [Matrix.sub_apply] using this
  have hdec : a = δ * (1 - e) + e * a := by linear_combination (-1 : AF F ⊗[F] E) * hfix
  rw [hdec, GlobalTheory.T.idempotentAdeleOfPlaces_mul_eq_sum_components S₁ S₂ ε hε a, ← add_assoc]
  refine Set.add_mem_add (Set.add_mem_add ⟨δ, ?_, rfl⟩ (Set.finsetSum_mem_finsetSum _ _ _ fun w hw => ⟨_, ?_, rfl⟩))
    (Set.finsetSum_mem_finsetSum _ _ _ fun v hv => ⟨_, ?_, rfl⟩)
  · rw [hδ, Matrix.one_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact hC₁' w hw _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j
  · exact hC₂' v hv _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j

end GlobalTheory.SUSuppCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompact
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem isCompact_setOf_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C);
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K →
      IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  letI tA : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := T2Space.of_injective_continuous (basV G v).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap)
  have hst1 : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sL : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun y => (starT G.star (Qv v) y).unop
      map_add' := fun x y => by simp
      map_smul' := fun r y => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hst1]
        exact (Algebra.commutes r _).symm }
  have hsc : Continuous sL := IsModuleTopology.continuous_of_linearMap sL
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := Qv v) (s := ({()} : Set Unit))
    (v := fun _ : Unit => (1 : Qv v ⊗[ℚ] G.C)) (by
      rw [linearIndepOn_singleton_iff]; exact one_ne_zero)
  have hf1 : f 1 = 1 := hf () rfl
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have key : ∀ d : Gv G v, f (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C) *
      sL ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)) =
      (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    intro d
    have hd : (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := d.2
    show f (_ * (starT G.star (Qv v) _).unop) = _
    rw [hd, Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_eq_mul, mul_one]
  set L1 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ => f ((u : Qv v ⊗[ℚ] G.C) * sL u)) '' K with hL1
  set L2 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ =>
    f (((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sL ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))) '' K with hL2
  have hL1c : IsCompact L1 := hK.image (hfc.comp (Units.continuous_val.mul (hsc.comp Units.continuous_val)))
  have hL2c : IsCompact L2 := hK.image (hfc.comp (Units.continuous_coe_inv.mul (hsc.comp Units.continuous_coe_inv)))
  set T : Set (Qv v)ˣ := Units.embedProduct (Qv v) ⁻¹' (L1 ×ˢ (MulOpposite.op '' L2)) with hT
  have hTc : IsCompact T :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hL1c.prod (hL2c.image MulOpposite.continuous_op))
  set Z : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ) := {x | ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      sL ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((x.2 : (Qv v)ˣ) : Qv v)} with hZ
  have hZc : IsClosed Z := isClosed_eq
    ((Units.continuous_val.comp continuous_fst).mul (hsc.comp (Units.continuous_val.comp continuous_fst)))
    ((continuous_algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (Units.continuous_val.comp continuous_snd))
  have himg : Subtype.val '' {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} = (K ×ˢ T) ∩ Z := by
    ext x
    constructor
    · rintro ⟨d, hdK, rfl⟩
      have k2 := key d⁻¹
      simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv] at k2
      refine ⟨⟨hdK, ?_⟩, d.2⟩
      show Units.embedProduct (Qv v) _ ∈ L1 ×ˢ (MulOpposite.op '' L2)
      rw [Units.embedProduct_apply]
      exact ⟨⟨_, hdK, key d⟩, ⟨_, ⟨_, hdK, k2⟩, rfl⟩⟩
    · rintro ⟨⟨hK1, -⟩, hZ1⟩
      exact ⟨⟨x, hZ1⟩, hK1, rfl⟩
  exact Subtype.isCompact_iff.2 (himg ▸ (hK.prod hTc).inter_right hZc)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

def iotaF (G : HTGroup p) (v : AwayP p) : Qv v ⊗[ℚ] G.F →ₐ[Qv v] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id (Qv v) (Qv v)) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem iotaF_tmul (G : HTGroup p) (v : AwayP p) (a : Qv v) (x : G.F) :
    iotaF G v (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] algebraMap G.F G.C x := rfl

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem isIntV_add' (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact add_mem (ha i) (hb i)

theorem isIntV_neg (G : HTGroup p) (v : AwayP p) {a : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a) :
    IsIntV G v (-a) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (ha i)

theorem isIntV_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (f : ι → Qv v ⊗[ℚ] G.C)
    (h : ∀ i ∈ s, IsIntV G v (f i)) : IsIntV G v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isIntV_zero G v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntV_add' G v (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Subring (Qv v ⊗[ℚ] G.F) where
  carrier := {m | IsIntV G v (iotaF G v m)}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact h1
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_mul] at *; exact hm _ _ ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact isIntV_zero G v
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_add] at *; exact isIntV_add' G v ha hb
  neg_mem' {a} ha := by simp only [Set.mem_setOf_eq, map_neg] at *; exact isIntV_neg G v ha

theorem mem_intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) (m : Qv v ⊗[ℚ] G.F) :
    m ∈ intF G v h1 hm ↔ IsIntV G v (iotaF G v m) := Iff.rfl

end GlobalTheory.OrbFinAf
end
end

