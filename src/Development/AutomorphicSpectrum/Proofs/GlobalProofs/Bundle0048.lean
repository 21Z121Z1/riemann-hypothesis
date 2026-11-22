import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0047
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika
section
open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Published

section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem latticeCurve_eq_weierstrassCurve (L : PeriodPair) :
    GlobalTheory.latticeCurve L = weierstrassCurve L := by
  simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]

theorem j_eq_of_eq {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

theorem latticeCurve_j (L : PeriodPair) : (GlobalTheory.latticeCurve L).j = (weierstrassCurve L).j :=
  j_eq_of_eq (latticeCurve_eq_weierstrassCurve L)

theorem under_ne_bot (M : IntermediateField K ℂ) [NumberField M] {P : Ideal (𝓞 M)} (hP : P ≠ ⊥) :
    P.under (𝓞 K) ≠ ⊥ :=
  fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)

theorem isUnramifiedAbelian_hilbertClassField :
    GlobalTheory.Published.IsUnramifiedAbelian (hilbertClassField K ℂ) := by
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  refine ⟨inferInstance, inferInstance, fun P hp hP => ?_⟩
  let v : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, under_ne_bot _ hP⟩
  exact (isUnramifiedEverywhere_hilbertClassField K ℂ).1 v P hp ⟨rfl⟩

theorem isUnramifiedEverywhere_of_isUnramifiedAbelian [IsTotallyComplex K]
    {M : IntermediateField K ℂ} [NumberField M] (h : GlobalTheory.Published.IsUnramifiedAbelian M) :
    IsUnramifiedEverywhere K M := by
  refine ⟨fun v P hp hv => ?_, fun v w hw => ?_⟩
  · exact h.2.2 P (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P)
  · exact InfinitePlace.isUnramified_iff.2 (Or.inr (hw ▸ IsTotallyComplex.isComplex v))

theorem isHilbertClassField_hilbertClassField [IsTotallyComplex K] :
    GlobalTheory.Published.IsHilbertClassField (hilbertClassField K ℂ) := by
  refine ⟨isUnramifiedAbelian_hilbertClassField, fun M hM => ?_⟩
  have := hM.1
  have := hM.2.1
  have : NumberField M := NumberField.of_module_finite K _
  exact (le_hilbertClassField_iff K ℂ M).2 (isUnramifiedEverywhere_of_isUnramifiedAbelian hM)

theorem isArtinMap_hilbertClassFieldArtinEquiv :
    GlobalTheory.Published.IsArtinMap (hilbertClassFieldArtinEquiv K ℂ).toMonoidHom := by
  intro 𝔭 𝔓 hP hO
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  have hne : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 𝔭.2
  have hpp : (𝔭 : Ideal (𝓞 K)).IsPrime := by
    rw [hO.over]
    exact Ideal.IsPrime.under _ _
  let v : HeightOneSpectrum (𝓞 K) := ⟨𝔭, hpp, hne⟩
  let w : HeightOneSpectrum (𝓞 (hilbertClassField K ℂ)) :=
    ⟨𝔓, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne 𝔓⟩
  have hwv : w.asIdeal.LiesOver v.asIdeal := hO
  have : Finite (𝓞 (hilbertClassField K ℂ) ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have e : hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭) = _ :=
    hilbertClassFieldArtinEquiv_mk0 K ℂ v w
  change IsArithFrobAt (𝓞 K) (hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭)) w.asIdeal
  rw [e]
  exact IsArithFrobAt.arithFrobAt _ _ _

theorem lattice_eq_idealLattice {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair}
    (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) : L.lattice = idealLattice (algebraMap K ℂ) 𝔞.1 :=
  SetLike.coe_injective h

theorem latticeEnd_eq_cmRing [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair} (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) :
    latticeEnd L = cmRing (algebraMap K ℂ) := by
  rw [← latticeEnd_ideal (algebraMap K ℂ) hK 𝔞]
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔
    ∀ l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice,
      α * l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice
  have e : (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice = L.lattice := by
    rw [lattice_eq_idealLattice h]
    exact lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  rw [e]

end

theorem complexMultiplicationJ : GlobalTheory.Published.ComplexMultiplicationJSt := by
  intro K _ _ _ _ hK
  refine ⟨hilbertClassField K ℂ, hilbertClassFieldArtinEquiv K ℂ,
    isHilbertClassField_hilbertClassField, isArtinMap_hilbertClassFieldArtinEquiv, ?_, ?_⟩
  · intro 𝔞 L hL
    rw [latticeCurve_j]
    exact adjoin_j_curve_eq_hilbertClassField hK
      (CMCurve.ofLattice (algebraMap K ℂ) L (latticeEnd_eq_cmRing hK hL))
  · intro 𝔞 𝔟 L L' hL hL' x hx
    have hE := latticeEnd_eq_cmRing hK hL
    have hlat : L'.lattice = idealLattice (algebraMap K ℂ) ↑𝔟⁻¹ * L.lattice := by
      rw [lattice_eq_idealLattice hL', lattice_eq_idealLattice hL, Units.val_mul, idealLattice_mul]
    rw [latticeCurve_j] at hx ⊢
    have hx' : x = ⟨(weierstrassCurve L).j, j_weierstrassCurve_mem_hilbertClassField hK L hE⟩ :=
      Subtype.ext hx
    rw [hx']
    exact hilbertClassFieldArtinEquiv_apply_j_weierstrassCurve hK L L' hE 𝔟 hlat

end GlobalTheory.CompanionTheory.Published
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_hasSupport (hBZ : BernsteinZelevinskyFiniteness) (hG : GeometricLemma) (x : IrrGL k) :
    ∃ s, HasSupport x.rep s := by
  obtain ⟨s, d, σ, h⟩ := GlobalTheory.CuspSupportExist.main hBZ hG k x.1 (Irr.ofIrrRep x.2.rep)
  exact ⟨_, hasSupport_of_isCuspSupport h⟩

theorem map_univ_eq_sum {α : Type} {β : Type*} [Fintype α] (f : α → β) :
    Finset.univ.val.map f = ∑ a, ({f a} : Multiset β) := by
  rw [Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem hasSupport_of_isSubquotient_prodIrr {c N : ℕ} {y : Fin c → IrrGL k}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL k)} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) := by
  choose T u hu hc using ht
  have h3 := fun a => (hc a).2.2
  choose e' he' using h3
  let e := stdBlocks (fun a => (y a).1) hd
  have step1 : IsSubquotient (multiProd e fun a => (y a).rep)
      (multiProd e fun a => multiProd (e' a) fun b => (u a b).rep) :=
    GlobalTheory.CuspSupportExist.L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (GlobalTheory.CuspSupportExist.L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := GlobalTheory.CuspSupportExist.L_stage k c N (fun a => (y a).1) e T (fun a b => (u a b).1) e' _
    (fun a b => (u a b).rep) fun a b => (u a b).2.rep.smooth
  refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, ?_, hi,
    fun c => (hc _).2.1 _, E, h.trans (step1.trans hE)⟩
  rw [map_univ_eq_sum, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (T a)) => ({u p.1 p.2} : Multiset _)),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hu a, map_univ_eq_sum]

theorem exists_sum_of_jac (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (hs : HasSupport π s) {r : ℕ} {d : Fin r → ℕ}
    (e' : (Σ j, Fin (d j)) ≃ Fin N) {τ : Representation ℂ (Levi k fun j => Fin (d j)) W} (hτ : τ.IsIrreducible)
    (hτs : IsSubquotient τ (jac e' π)) (y : ∀ j, IrrRep (GL (Fin (d j)) k))
    (hy : ∀ j, IsSubquotient (y j).ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W)) :
    ∃ t : Fin r → Multiset (IrrGL k), (∀ j, HasSupport (y j).ρ (t j)) ∧ s = ∑ j, t j := by
  obtain ⟨h, x, rfl, hi, hc, e, hsub⟩ := hs
  have hx : ∀ i, (x i).IsCusp := fun i => ⟨(hc i).1, (hc i).2.2⟩
  obtain ⟨b, f, g, c, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e'
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ
    (hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_parInd _ _) hsub))
  choose J hJ0 hJ using fun i => exists_block_of_isCusp (hx i) (f i) (c i) (hrow i)
  let u : Fin h → Fin r → Multiset (IrrGL k) := fun i j => if j = J i then {x i} else 0
  have hu : ∀ i j, HasSupport (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr).rep (u i j) := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      simp only [u, if_true]
      rw [hJ i]
      exact hasSupport_self (hx i)
    · obtain ⟨s', hs'⟩ := exists_hasSupport hBZ hG (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr)
      simp only [u, if_neg hj]
      rwa [eq_zero_of_hasSupport (hJ0 i j hj) hs'] at hs'
  refine ⟨fun j => ∑ i, u i j, fun j => ?_, ?_⟩
  · have hd : ∑ i, b.1 i j = d j := by simpa using b.2.2 j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (c i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (c i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (c i j).ρ) (fun i => (c i j).smooth) fun i => (c i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr) (fun i => hu i j) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  · rw [Finset.sum_comm]
    simp only [u, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map x), Multiset.map_map]
    rfl

theorem eq_of_hasSupport (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (N : ℕ) :
    ∀ (x : IrrGL k), x.1 = N → ∀ s t : Multiset (IrrGL k), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s t hs ht
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · rw [eq_zero_of_hasSupport h0 hs, eq_zero_of_hasSupport h0 ht]
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs, eq_singleton_of_isCusp ⟨hpos, hc⟩ ht]
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hs e hτ hτs y hy
    obtain ⟨u', hu', rfl⟩ := exists_sum_of_jac hG hBZ ht e hτ hτs y hy
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : d j < x.1 := by
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    exact ih (d j) hlt (IrrGL.of (y j).ρ (y j).smooth (y j).irr) rfl _ _
      ((hu j).of_equiv (IrrGL.equivOf _ _ _)) ((hu' j).of_equiv (IrrGL.equivOf _ _ _))

theorem hasSupport_unique (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s t : Multiset (IrrGL k)} (hs : HasSupport π s)
    (ht : HasSupport π t) : s = t := by
  have φ := IrrGL.equivOf π hs.isSmooth hs.isIrreducible
  exact eq_of_hasSupport hG hBZ N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t (hs.of_equiv φ) (ht.of_equiv φ)

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicSectionModerateGrowth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem continuous_section_polynomial_growth_of_isProper : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens), IsAffineOpen V → V ≤ B.U i → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V hVa hV
  have := compactSpace_cxPts_of_isProper Y p hp
  obtain ⟨n, u, hu⟩ := GlobalTheory.T.regular_function_polynomial_growth Y p inferInstance inferInstance V hVa
  refine ⟨n, u, ?_⟩
  have h0 (y) : 0 ≤ ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine SectionGrowth.global_bound _ (fun y => ‖s i y‖) _ (fun y => le_add_of_nonneg_right (h0 y)) fun y₀ => ?_
  obtain ⟨j, hj⟩ := exists_mem_ptsIn hB.cover y₀
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := B.U j) (mem_ptsIn.1 hj)
  have h2 : W ≤ B.U j := hle
  have hW₀ : y₀ ∈ ptsIn p (RingHom.id ℂ) W := mem_ptsIn.2 hxW
  have h3 : V ⊓ W ≤ B.U i ⊓ B.U j := inf_le_inf hV h2
  obtain ⟨r, m, w, hb⟩ := hu W hW (resG Y h3 (B.g i j).val)
  have hn := (isOpen_ptsIn W).mem_nhds hW₀
  let F : CxPts p (RingHom.id ℂ) → ℝ := fun y => (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * ‖s j y‖
  have hF : ContinuousAt F y₀ :=
    (tendsto_finset_sum _ fun k _ => ((continuousOn_ev (w k)).continuousAt hn).norm).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hj)).norm
  refine ⟨|F y₀| + 1, m, by positivity, ?_⟩
  filter_upwards [hn, hF.eventually (eventually_le_nhds (lt_of_le_of_lt (le_abs_self _) (lt_add_one |F y₀|)))]
    with y hy hFy hyV
  have hVW : y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W) := mem_ptsIn_inf.2 ⟨hyV, hy⟩
  have hb' := hb y hVW
  have hij : y ∈ ptsIn p (RingHom.id ℂ) (B.U i ⊓ B.U j) := ptsIn_mono h3 hVW
  have e : ev p (RingHom.id ℂ) (V ⊓ W) (resG Y h3 (B.g i j).val) y = ev p (RingHom.id ℂ) (B.U i ⊓ B.U j) (B.g i j).val y :=
    ev_res _ hVW _
  rw [e] at hb'
  rw [hs.1 i j y (ptsIn_mono hV hyV) (ptsIn_mono h2 hy), CxPts.gv, norm_mul]
  have hT : 0 ≤ (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := pow_nonneg (add_nonneg zero_le_one (h0 y)) _
  calc _ ≤ ((∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m) * ‖s j y‖ :=
        mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
    _ = F y * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by simp only [F]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hFy hT

end GlobalTheory.CompanionTheory.Gaga
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def mnorm (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖

def wt (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (gᴴ * g).trace.re

def IsSmoothVec (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ F : (Fin n → Fin n → ℂ) → H, ContDiff ℝ ∞ F ∧ ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z

def WordBound (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
    ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod

def AlmostIsom (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ (Q : H → H → ℂ) (m M a : ℝ), 0 < m ∧ 0 ≤ M ∧ 0 ≤ a ∧
    (∀ x y z, Q x (y + z) = Q x y + Q x z) ∧ (∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) ∧
    (∀ x y, Q y x = star (Q x y)) ∧ (∀ x, m * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, ‖Q x y‖ ≤ M * ‖x‖ * ‖y‖) ∧
    ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H),
      (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤
        Real.exp (a * |t| * mnorm X) * (Q x x).re

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

