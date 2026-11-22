import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamUnifHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SFour

theorem pow_le_map {V V' : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing V'] [IsLocalRing V']
    (io : V →+* V') (hfin : io.Finite) :
    ∃ J : ℕ, ∀ j : ℕ, maximalIdeal V' ^ (J * j) ≤ (maximalIdeal V ^ j).map io := by
  letI := io.toAlgebra
  haveI : Module.Finite V V' := hfin
  obtain ⟨E, hE⟩ := GlobalTheory.Poinc.OrbTrace.exists_pow_le (A := V) (B := V') (maximalIdeal V') (maximalIdeal.isMaximal V') 1
  have h1 : maximalIdeal V' ^ E ≤ (maximalIdeal V).map io := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hE x hx
    have hu' : IsUnit u := by
      by_contra h
      exact hu ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [pow_one] at hux
    exact (Ideal.unit_mul_mem_iff_mem _ hu').1 hux
  refine ⟨E, fun j => ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono h1 j

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A]
  [IsLocalRing A]

theorem term_mem (Φ : VPre bar q W A) (y : Φ.Y) (mu : Fin s → Φ.X y) (cc : Φ.Q) (j : ℕ)
    (hj : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) : Φ.term y mu cc ∈ maximalIdeal (Φ.V y) ^ j := by
  have hnn : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have hle : j ≤ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    have e1 : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnn i)
    rw [← e1] at hj
    exact_mod_cast hj
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _

end GlobalTheory.Poinc.SFour

namespace GlobalTheory.Poinc.SFour

theorem four_of_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.ClassSums N₁ → Φ.Four N₁ := by
  intro O _ bar q s W A _ _ _ _ Φ N₁ hcs y₀ N₀
  classical
  obtain ⟨N, hN0, hN1, hNd, k, hk0, hk, L, _, _, _, _, _, _, 𝔷, f, hz, hf, hy, hσ⟩ := hcs y₀ N₀
  refine ⟨N, hN0, hNd, k, hk0, hk, fun l a c e => ?_⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := OrbTrace.exists_classes (O := O) (N₁ := N₁) hN1 a
  set F : integralClosure A L := ∑ c' ∈ C, ∏ i, f (fun u => c' (i, u)) (c i) with hF
  have hFix : ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
      σ (F : L) = F := by
    intro σ hσ'
    obtain ⟨ga, h1, h2, h3, h4⟩ := hσ σ hσ'
    have e1 : ((F : integralClosure A L) : L) = ∑ c' ∈ C, ∏ i, (f (fun u => c' (i, u)) (c i) : L) := by
      rw [hF]; push_cast; rfl
    rw [e1, map_sum]
    simp only [map_prod, h4]
    exact OrbTrace.sum_comp_eq C hC1 hC2 hC3 ga h1 h2 h3 (fun c' => ∏ i, (f (fun u => c' (i, u)) (c i) : L))
      (fun c₁ c₂ h => Finset.prod_congr rfl fun i _ => by rw [hf _ _ _ fun u => h _])
  haveI := hz
  obtain ⟨g₀, b, hb, hbF⟩ := GlobalTheory.DecompFixed.exists_approx_integralClosure A (FractionRing A) L 𝔷 F hFix e
  refine ⟨g₀, fun y j => ?_⟩
  obtain ⟨V', _, _, io, ev', hfin, hloc, hpure, hcomm, hcomap, hcls⟩ := hy y
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  obtain ⟨J, hJ⟩ := pow_le_map io hfin
  set j' := J * j + j with hj'
  have hjj : j ≤ j' := Nat.le_add_left _ _
  have hJj : maximalIdeal V' ^ j' ≤ (maximalIdeal (Φ.V y) ^ j).map io :=
    (Ideal.pow_le_pow_right (Nat.le_add_right _ _)).trans (hJ j)
  have hmap : ∀ n, (maximalIdeal (Φ.V y) ^ n).map io ≤ maximalIdeal V' ^ n := by
    intro n
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 <|
      (IsLocalRing.mem_maximalIdeal _).2 fun h => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit io x h)) n
  choose S₀ hSa hSb hSc using fun κ cc => hcls κ cc j'
  set T : Finset (Fin s → Φ.X y) := C.biUnion (fun c' => Finset.univ.biUnion
    (fun i => S₀ (fun u => c' (i, u)) (c i))) with hT
  have hSfin : {mu : Fin l × Fin s → Φ.X y | mu ∈ orbit O N₁ N (k y) a ∧ ∀ i, (fun u => mu (i, u)) ∈ T}.Finite := by
    refine ((Set.Finite.pi' (fun _ : Fin l => T.finite_toSet)).image (fun x j => x j.1 j.2)).subset ?_
    intro mu hmu
    exact ⟨fun i u => mu (i, u), hmu.2, rfl⟩
  refine ⟨hSfin.toFinset, fun mu hmu => (hSfin.mem_toFinset.1 hmu).1, fun mu hmu hmuS => ?_, ?_⟩
  · rw [hSfin.mem_toFinset] at hmuS
    obtain ⟨i, hi⟩ : ∃ i, (fun u => mu (i, u)) ∉ T := by
      by_contra hcon
      push_neg at hcon
      exact hmuS ⟨hmu, hcon⟩
    obtain ⟨gm, g1, g2, g3, g4⟩ := hmu
    obtain ⟨c', hc', hcc⟩ := hC3 (fun idx => gm (a idx)) ⟨gm, g1, g2, g3, fun idx => OrbTrace.cm_refl _⟩
    have hcong : ∀ v, CongMod N (mu (i, v)) (k y (c' (i, v))) := fun v =>
      OrbTrace.cm_trans (g4 _) (OrbTrace.cm_map (k y) (OrbTrace.cm_symm (hcc _)))
    have hnot : (fun u => mu (i, u)) ∉ S₀ (fun u => c' (i, u)) (c i) := fun h =>
      hi (Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩⟩)
    have h1 := hSb (fun u => c' (i, u)) (c i) (fun u => mu (i, u)) hcong hnot
    have hnn : ∀ fi i', 0 ≤ qW W (Φ.δ y fi) (fun u => mu (i', u)) := fun fi i' =>
      qW_nonneg Φ.posW (Φ.bal y fi).1 (Φ.nonneg y fi) _
    calc (j : ℤ) ≤ j' := by exact_mod_cast hjj
      _ ≤ ∑ fi, qW W (Φ.δ y fi) (fun u => mu (i, u)) := h1
      _ ≤ ∑ fi, lin W mu (Φ.δ y fi) := Finset.sum_le_sum fun fi _ =>
          Finset.single_le_sum (f := fun i' => qW W (Φ.δ y fi) (fun u => mu (i', u))) (fun i' _ => hnn fi i')
            (Finset.mem_univ i)
  · have key : ∀ c' ∈ C, ∀ i (U : Finset (Fin s → Φ.X y)), S₀ (fun u => c' (i, u)) (c i) ⊆ U →
        (∀ ν ∈ U, ∀ v, CongMod N (ν v) (k y (c' (i, v)))) →
        ev' (f (fun u => c' (i, u)) (c i)) - io (∑ ν ∈ U, Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν) ∈
          maximalIdeal V' ^ j' := by
      intro c' hc' i U hU hU'
      rw [← Finset.sum_sdiff hU, map_add]
      have e2 : ∀ x y z : V', x - (y + z) = (x - z) - y := fun _ _ _ => by ring
      rw [e2]
      refine sub_mem (hSc _ _) (hmap j' (Ideal.mem_map_of_mem io (Ideal.sum_mem _ fun ν hν => ?_)))
      obtain ⟨hνU, hνS⟩ := Finset.mem_sdiff.1 hν
      exact term_mem Φ y ν (c i) j' (hSb _ _ ν (hU' ν hνU) hνS)
    have hsum := OrbTrace.sum_orbit_eq C hC1 hC2 hC3 (k y) (hk y) T hSfin.toFinset (fun mu => hSfin.mem_toFinset)
      (fun i ν => Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν)
    have hF' : ev' F - io (∑ mu ∈ hSfin.toFinset, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) *
        mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v))) ∈ maximalIdeal V' ^ j' := by
      rw [hsum]
      rw [← Ideal.Quotient.eq]
      rw [hF, map_sum ev', map_sum io, map_sum (Ideal.Quotient.mk _), map_sum (Ideal.Quotient.mk _)]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      rw [map_prod ev', map_prod io, map_prod (Ideal.Quotient.mk _), map_prod (Ideal.Quotient.mk _)]
      refine Finset.prod_congr rfl fun i _ => Ideal.Quotient.eq.2 (key c' hc' i _ ?_ ?_)
      · intro ν hν
        exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hν⟩⟩,
          hSa _ _ ν hν⟩
      · intro ν hν
        exact (Finset.mem_filter.1 hν).2
    have hD : ev' F - io (Φ.ev y g₀) ∈ ((maximalIdeal A ^ e).map (Φ.ev y)).map io := by
      have h1 := Ideal.mem_map_of_mem ev' hbF
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, map_mul, map_sub] at h1
      have hu : IsUnit (ev' b) := by
        by_contra h
        exact hb (by rw [← hcomap]; exact Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have h2 := (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
      have h3 : ev' (algebraMap A (integralClosure A L) g₀) = io (Φ.ev y g₀) := RingHom.congr_fun hcomm g₀
      rwa [h3] at h2
    rw [← hpure (maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y))]
    refine Ideal.mem_comap.2 ?_
    rw [Ideal.map_sup, map_sub]
    have h4 := sub_mem (Ideal.mem_sup_left (T := ((maximalIdeal A ^ e).map (Φ.ev y)).map io) (hJj hF'))
      (Ideal.mem_sup_right (S := (maximalIdeal (Φ.V y) ^ j).map io) hD)
    rwa [sub_sub_sub_cancel_left] at h4

end GlobalTheory.Poinc.SFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SepLam

theorem mem_of_forall_mem_sup_pow {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (I : Ideal V) (hI : I ≠ ⊤)
    (z : V) (h : ∀ j : ℕ, z ∈ I ⊔ maximalIdeal V ^ j) : z ∈ I := by
  haveI : Nontrivial (V ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (V ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal V).map (Ideal.Quotient.mk I) ≤ maximalIdeal (V ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr fun x hx hu => hx (isUnit_of_map_unit (Ideal.Quotient.mk I) x hu)
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (V ⧸ I)) (Ideal.IsMaximal.ne_top inferInstance)
  have hz : Ideal.Quotient.mk I z ∈ ⨅ j : ℕ, maximalIdeal (V ⧸ I) ^ j := by
    refine Ideal.mem_iInf.mpr fun j => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h j)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    refine pow_le_pow_left' hmax j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact hz

end GlobalTheory.Poinc.SepLam

namespace GlobalTheory.Poinc.SepLam

theorem lam_of_exact : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  intro O _ bar q s W A _ _ Φ N₁ hs hN hE
  classical
  refine ⟨(W ⟨0, hs⟩ ⟨0, hs⟩).toNat, fun y hm i x hx => ?_⟩
  haveI : Subsingleton (Fin (Φ.m y)) := by rw [hm]; infer_instance
  have hsym : ∀ a b, Φ.δ y i a b = Φ.δ y i b a := (Φ.bal y i).1
  have hδpos : ∀ z, z ≠ 0 → 0 < Φ.δ y i z z := fun z hz => by
    obtain ⟨k, hk⟩ := Φ.pos y z hz
    rwa [Subsingleton.elim k i] at hk
  obtain ⟨c0, hc0, hge⟩ := QWDom.qW_ge s W Φ.posW
  have hqpos : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → 0 < qW W (Φ.δ y i) mu := by
    intro mu hmu
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hmu
    have h1 : Φ.δ y i (mu v) (mu v) ≤ ∑ u, Φ.δ y i (mu u) (mu u) :=
      Finset.single_le_sum (f := fun u => Φ.δ y i (mu u) (mu u)) (fun u _ => Φ.nonneg y i _) (Finset.mem_univ v)
    have h2 : (0 : ℝ) < c0 * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) :=
      mul_pos hc0 (by exact_mod_cast (hδpos _ hv).trans_le h1)
    have h3 := hge (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) mu
    exact_mod_cast h2.trans_le h3
  have hqnn : ∀ mu : Fin s → Φ.X y, 0 ≤ qW W (Φ.δ y i) mu := fun mu =>
    GlobalTheory.Poinc.qW_nonneg Φ.posW hsym (Φ.nonneg y i) mu

  have hsne : (Pi.single ⟨0, hs⟩ x : Fin s → Φ.X y) ≠ 0 := fun h0 => hx (by simpa using congrFun h0 ⟨0, hs⟩)
  have hP : ∃ n : ℕ, ∃ mu : Fin s → Φ.X y, mu ≠ 0 ∧ (qW W (Φ.δ y i) mu).toNat = n :=
    ⟨_, Pi.single ⟨0, hs⟩ x, hsne, rfl⟩
  obtain ⟨mu₀, hmu₀, hq₀⟩ := Nat.find_spec hP
  have hmin : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → qW W (Φ.δ y i) mu₀ ≤ qW W (Φ.δ y i) mu := by
    intro mu hmu
    have h1 := Nat.find_min' hP ⟨mu, hmu, rfl⟩
    rw [← hq₀] at h1
    have := hqnn mu₀
    have := hqnn mu
    omega
  have hlead : ∀ nu : Fin s → Φ.X y, nu ≠ 0 → qW W (Φ.δ y i) mu₀ < qW W (Φ.δ y i) (mu₀ + N₁ • nu) :=
    fun nu hnu => GlobalTheory.T.least_vector_unique_in_class_mod s W Φ.posW (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) ⊤ (fun mu _ h => hqpos mu h)
      mu₀ trivial hmu₀ (fun mu _ h => hmin mu h) N₁ hN nu trivial hnu
  set n₀ := (qW W (Φ.δ y i) mu₀).toNat with hn₀
  have hn₀z : (n₀ : ℤ) = qW W (Φ.δ y i) mu₀ := Int.toNat_of_nonneg (hqnn mu₀)
  have hn₀pos : 1 ≤ n₀ := by have := hqpos mu₀ hmu₀; omega
  have hmono : ∀ mu : Fin s → Φ.X y, mono W (Φ.t y) (Φ.δ y) mu = Φ.t y i ^ (qW W (Φ.δ y i) mu).toNat := by
    intro mu
    rw [mono, Fintype.prod_subsingleton _ i]
  have hsum : ∀ mu : Fin s → Φ.X y, ∑ k, qW W (Φ.δ y k) mu = qW W (Φ.δ y i) mu := fun mu =>
    Fintype.sum_subsingleton _ i
  obtain ⟨c, hc⟩ := Φ.u_unit y mu₀
  obtain ⟨h, hh⟩ := hE y mu₀ c
  have htm := (Φ.t_mem y i).1
  have hI : Ideal.span {Φ.t y i ^ (n₀ + 1)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ htm _ (Nat.succ_pos _)) hu
  have key : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ ∈ Ideal.span {Φ.t y i ^ (n₀ + 1)} := by
    haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
    refine mem_of_forall_mem_sup_pow _ hI _ fun j => ?_
    obtain ⟨S, hS1, hS2, hS3⟩ := hh (max j (n₀ + 1))
    have hmem : mu₀ ∈ S := by
      by_contra hn
      have := hS2 mu₀ (fun v => ⟨0, by simp⟩) hn
      rw [hsum] at this
      omega
    have hsplit : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ =
        ∑ mu ∈ S.erase mu₀, Φ.term y mu c + (Φ.ev y h - RingHom.id _ (∑ mu ∈ S, Φ.term y mu c)) := by
      rw [← Finset.add_sum_erase S _ hmem, VPre.term, hmono, RingHom.id_apply]
      ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun mu hmu => ?_)
      (Ideal.pow_le_pow_right (le_max_left j (n₀ + 1)) hS3)
    obtain ⟨hne, hmuS⟩ := Finset.mem_erase.mp hmu
    have hcong := hS1 mu hmuS
    set nu : Fin s → Φ.X y := fun v => (hcong v).choose
    have hmu_eq : mu = mu₀ + N₁ • nu := funext fun v => (hcong v).choose_spec
    have hnu : nu ≠ 0 := by
      rintro h0
      rw [h0, smul_zero, add_zero] at hmu_eq
      exact hne hmu_eq
    have hlt := hlead nu hnu
    rw [← hmu_eq] at hlt
    rw [VPre.term, hmono, Ideal.mem_span_singleton]
    refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
    have := hqnn mu
    omega
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp key
  have hev : Φ.ev y h = Φ.t y i ^ n₀ * (Φ.u y mu₀ c + r * Φ.t y i) := by linear_combination -hr
  have hunit : IsUnit (Φ.u y mu₀ c + r * Φ.t y i) := by
    by_contra hu
    have h1 : Φ.u y mu₀ c + r * Φ.t y i ∈ maximalIdeal (Φ.V y) := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have h2 := (maximalIdeal (Φ.V y)).sub_mem h1 ((maximalIdeal (Φ.V y)).mul_mem_left r htm)
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hc
  have hevm : Φ.ev y h ∈ maximalIdeal (Φ.V y) := by
    rw [hev]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ htm _ hn₀pos)
  refine ⟨h, ?_, ?_⟩
  · by_contra hA
    have hu : IsUnit h := by
      by_contra hu'
      exact hA ((IsLocalRing.mem_maximalIdeal _).mpr hu')
    exact (IsLocalRing.mem_maximalIdeal _).mp hevm (hu.map (Φ.ev y))
  · have hd : Φ.ev y h ∣ Φ.t y i ^ n₀ := by
      rw [hev]
      exact (hunit.mul_right_dvd).mpr dvd_rfl
    refine hd.trans (pow_dvd_pow _ ?_)
    have hsingle : qW W (Φ.δ y i) (Pi.single ⟨0, hs⟩ x) = W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x := by
      simp only [qW]
      rw [Finset.sum_eq_single ⟨0, hs⟩ (fun u _ hu => Finset.sum_eq_zero fun v _ => by
          simp [Pi.single_eq_of_ne hu]) (by simp),
        Finset.sum_eq_single ⟨0, hs⟩ (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
      simp
    have hle := hmin _ hsne
    rw [hsingle] at hle
    have hdx := hδpos x hx
    have hW : 0 < W ⟨0, hs⟩ ⟨0, hs⟩ := by
      by_contra hW
      push_neg at hW
      have : W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hW hdx.le
      omega
    zify
    rw [Int.toNat_of_nonneg hW.le, Int.toNat_of_nonneg hdx.le, hn₀z]
    exact hle

end GlobalTheory.Poinc.SepLam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum

variable {O : Type} [CommRing O]

section Abelian

variable {T : Scheme.{0}} {A : Over T} [GrpObj A]

def IsSelfDual (c : O →+* O) (i : OAct O A) (P : LB (A ⊗ A).left) : Prop :=
  IsDual A A P ∧ LBIso (swap P) P ∧
    ∀ x, LBIso (ev P (fst A A ≫ i.act x) (snd A A)) (ev P (fst A A) (snd A A ≫ i.act (c x)))

def actPull (i : OAct O A) (x : O) {V : T.Opens} (hV : IsAffineOpen V) :
    primDR (onAff A hV) →ₗ[Γ(T, V)] primDR (onAff A hV) :=
  haveI := i.hom x
  primPull (dp0 Γ(T, V)) (𝟙 _) (A := onAff A hV) (B := onAff A hV) ((Over.pullback hV.fromSpec).map (i.act x))

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

def IsDRAct (i : OAct O A) (ρ : O →+* End H) : Prop :=
  ∀ (x : O) (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
    e V hV ((VB.act ρ x).app V s) = actPull i x hV (e V hV s)

def IsHodgeIncl (a : omega A ⟶ H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(omega A, V)),
    e V hV (a.app V s) ∈ PrimitiveSubmodule (onAff A hV) ∧ HodgeSub.Corr A hV s (e V hV (a.app V s))

def IsPolPairing (P : LB (A ⊗ A).left) (β : H ⟶ dual H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V),
    ∃ (m : (onAff A hV ⊗ onAff A hV).left ⟶ (A ⊗ A).left)
      (φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V)),
      m ≫ (fst A A).left = (fst (onAff A hV) (onAff A hV)).left ≫ pullback.fst A.hom hV.fromSpec ∧
      m ≫ (snd A A).left = (snd (onAff A hV) (onAff A hV)).left ≫ pullback.fst A.hom hV.fromSpec ∧
      IsCorrForm (dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) (P.pull m) φ ∧ φ.IsPerfPair ∧
      ∀ (s : Γ(H, V)) (x y : HdR (onAff A hV)), (∀ t, x (e V hV t) = dualApp (β.app V s) le_rfl t) →
        φ x y = y (e V hV s)

variable (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0)

def IsLinFrob (Ψ : (frobPull p h0).obj H ⟶ H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
    e V hV (Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s)) =
      ConjSeq.frobDR p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV) (e V hV s)

omit e in

def IsDRDatum (i : OAct O A) (P : LB (A ⊗ A).left) (ρ : O →+* End H) (a : omega A ⟶ H) (b : H ⟶ Lie A)
    (u : (frobPull p h0).obj (Lie A) ⟶ H) (v : H ⟶ (frobPull p h0).obj (omega A)) : Prop :=
  ∃ (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)) (β : H ⟶ dual H)
    (Ψ : (frobPull p h0).obj H ⟶ H),
    IsDRIso A H e ∧ IsDRAct e i ρ ∧ IsHodgeIncl e a ∧ IsPolPairing e P β ∧ IsLinFrob e p h0 Ψ ∧
    b = β ≫ dualMap a ∧ (frobPull p h0).map b ≫ u = Ψ ∧
    v ≫ (frobPull p h0).map (cartierDualToBidual (omega A)) ≫ DualPull.theta (frob T p h0) (Lie A) = β ≫ dualMap u

end Abelian

section Res

variable {S T : Scheme.{0}} {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {A : Over T} [GrpObj A] {f : T ⟶ S}
  {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)
  (hT : (p : Γ(T, ⊤)) = 0) {g : ℕ} (hg : IsVB (omega G) g)

def omegaRes : (Scheme.Modules.pullback f).obj (omega G) ≅ omega A := asIso (omegaBase h)

def lieRes : (Scheme.Modules.pullback f).obj (Lie G) ≅ Lie A := @asIso _ _ _ _ (lieBase h) (isIso_lieBase h hg)

def frobLieRes : (Scheme.Modules.pullback f).obj ((frobPull p hS).obj (Lie G)) ≅ (frobPull p hT).obj (Lie A) :=
  (frobPullPullbackIso p hS f hT).app (Lie G) ≪≫ (frobPull p hT).mapIso (lieRes h hg)

def frobOmegaRes : (Scheme.Modules.pullback f).obj ((frobPull p hS).obj (omega G)) ≅ (frobPull p hT).obj (omega A) :=
  (frobPullPullbackIso p hS f hT).app (omega G) ≪≫ (frobPull p hT).mapIso (omegaRes h)

end Res

section On

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C T : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G) {A : Over T} [GrpObj A] {f : T ⟶ C}
  {φ : A.left ⟶ G.left}

omit [Fact q.Prime] in
include k in

theorem cast_eq_zero (f : T ⟶ C) : (q : Γ(T, ⊤)) = 0 := SS.FrobField.cast_zero_of_hom f (natCast_eq_zero C q k)

def IsDRDatumOn (j : OAct O A) (h : IsGrpPullback A G f φ) (P : LB (A ⊗ A).left) {g : ℕ} (hg : IsVB (omega G) g)
    (d : TwoSeq.DieuDatumOn q k c i g f) : Prop :=
  IsDRDatum q (cast_eq_zero q k f) j P d.ρ ((omegaRes h).inv ≫ d.a) (d.b ≫ (lieRes h hg).hom)
    ((frobLieRes h q (natCast_eq_zero C q k) (cast_eq_zero q k f) hg).inv ≫ d.u)
    (d.v ≫ (frobOmegaRes h q (natCast_eq_zero C q k) (cast_eq_zero q k f)).hom)

end On

section Ext

variable {X : Scheme.{0}} {F G : X.Modules}

theorem hom_ext_affine {φ ψ : F ⟶ G}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V), φ.app V s = ψ.app V s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover _ (fun U : {U : X.Opens // IsAffineOpen U ∧ U ≤ W} ↦ U.1)
    (fun U ↦ U.2.2) ?_ _ _ fun U ↦ ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hle⟩, hxU⟩
  · exact (QCoh.hom_app_res _ _ _).symm.trans ((h _ U.2.1 _).trans (QCoh.hom_app_res _ _ _))

theorem hom_dual_ext_affine {E : X.Modules} {φ ψ : E ⟶ dual F}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ (s : Γ(E, V)) (t : Γ(F, V)),
      dualApp (φ.app V s) le_rfl t = dualApp (ψ.app V s) le_rfl t) : φ = ψ := by
  refine hom_ext_affine fun V _ s ↦ dual_ext fun W hW t ↦ ?_
  refine AffinePairingGlue.fun_ext_affine fun U hU hUW ↦ ?_
  have k (χ : E ⟶ dual F) : resG X hUW (dualApp (χ.app V s) hW t) =
      dualApp (χ.app U (Twist.resM E (hUW.trans hW) s)) le_rfl (Twist.resM F hUW t) := by
    rw [Twist.app_resM, dualApp_res, dualApp_resM]
  rw [k, k, h U hU]

theorem frobPull_hom_ext_affine (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(X, ⊤)) = 0) {φ ψ : (frobPull p h0).obj F ⟶ G}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V),
      φ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s) =
        ψ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s)) : φ = ψ := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (frob X p h0)
  apply (adj.homEquiv _ _).injective
  refine hom_ext_affine fun V hV s ↦ ?_
  have k (χ : (frobPull p h0).obj F ⟶ G) : (adj.homEquiv _ _ χ).app V s =
      χ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s) := by
    rw [Adjunction.homEquiv_unit]
    exact congrArg (χ.app V) (QCoh.res_self _ (le_refl V) _).symm
  rw [k, k, h V hV]

end Ext

end GlobalTheory.AbDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transitive_on_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom → ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) → ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z), h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  first | exact @GlobalTheory.Mum.gal_transitive_on_fibres | exact GlobalTheory.Mum.gal_transitive_on_fibres | (intros; apply GlobalTheory.Mum.gal_transitive_on_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
section
namespace GlobalTheory.AnPer

theorem gaussManinPeriods_of_span_taylor : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods :=
  fun HS HT ↦ gaussManinPeriods_of_parts (-1) GlobalTheory.PeriodFamily.famUnif_holds GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.exists_integrationOverCyclesHom HS
    GlobalTheory.T.integrationOverCycles_lifts_lieLattice GlobalTheory.T.periodHom_push_end' GlobalTheory.T.pChern_neg_one GlobalTheory.T.fibrePeriod_eq_familyPeriod_value HT

end GlobalTheory.AnPer
end

