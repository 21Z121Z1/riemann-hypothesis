import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0463
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0456
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0467
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0471
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0399
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMass
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GenusRows

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V}
  {r k : ℕ} {P : Formalism.MainNotions.S.LocNG.FPair H r}

theorem rel_symm (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) {d d' : Formalism.MainNotions.S.LocNG.Datum P}
    (h : Formalism.MainNotions.S.LocNG.Datum.Rel d d') : Formalism.MainNotions.S.LocNG.Datum.Rel d' d := by
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum M hM H r k P hk hR
  obtain ⟨g, hg, hm⟩ := h
  have e1 : act.smul ⟨g, hg⟩ d = d' := (hmv ⟨g, hg⟩ d d').1 hm
  refine ⟨((⟨g, hg⟩ : P.UW0)⁻¹ : P.UW0).1, ((⟨g, hg⟩ : P.UW0)⁻¹ : P.UW0).2, (hmv _ d' d).2 ?_⟩
  letI := act
  rw [← e1]
  change ((⟨g, hg⟩ : P.UW0)⁻¹ : P.UW0) • ((⟨g, hg⟩ : P.UW0) • d) = d
  exact inv_smul_smul _ d

theorem rel_trans (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) {a b c : Formalism.MainNotions.S.LocNG.Datum P}
    (h1 : Formalism.MainNotions.S.LocNG.Datum.Rel a b) (h2 : Formalism.MainNotions.S.LocNG.Datum.Rel b c) :
    Formalism.MainNotions.S.LocNG.Datum.Rel a c := by
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum M hM H r k P hk hR
  obtain ⟨g, hg, hm⟩ := h1
  obtain ⟨g', hg', hm'⟩ := h2
  have e1 : act.smul ⟨g, hg⟩ a = b := (hmv ⟨g, hg⟩ a b).1 hm
  have e2 : act.smul ⟨g', hg'⟩ b = c := (hmv ⟨g', hg'⟩ b c).1 hm'
  refine ⟨((⟨g', hg'⟩ : P.UW0) * ⟨g, hg⟩ : P.UW0).1, ((⟨g', hg'⟩ : P.UW0) * ⟨g, hg⟩ : P.UW0).2,
    (hmv _ a c).2 ?_⟩
  letI := act
  rw [← e2, ← e1]
  change ((⟨g', hg'⟩ : P.UW0) * ⟨g, hg⟩) • a = (⟨g', hg'⟩ : P.UW0) • ((⟨g, hg⟩ : P.UW0) • a)
  exact mul_smul _ _ a

theorem eq_of_rel_reps (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) (R : Formalism.MainNotions.S.LocNG.Reps P) {d₁ d₂ y : Formalism.MainNotions.S.LocNG.Datum P}
    (h₁ : d₁ ∈ R.RD) (h₂ : d₂ ∈ R.RD) (r₁ : Formalism.MainNotions.S.LocNG.Datum.Rel d₁ y)
    (r₂ : Formalism.MainNotions.S.LocNG.Datum.Rel d₂ y) : d₁ = d₂ :=
  R.hRD.2.2 d₁ h₁ d₂ h₂ (rel_trans hM hk hR r₁ (rel_symm hM hk hR r₂))

theorem term_of_rel (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) {d d' : Formalism.MainNotions.S.LocNG.Datum P}
    (h : Formalism.MainNotions.S.LocNG.Datum.Rel d d') (ht : ∃ τ, Formalism.MainNotions.S.LocNG.IsTermOver P d τ) :
    ∃ τ, Formalism.MainNotions.S.LocNG.IsTermOver P d' τ := by
  obtain ⟨g, hg, hm⟩ := h
  obtain ⟨τ, hτ⟩ := ht
  exact ⟨_, (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data M hM H r k P hk hR g hg d d' τ hτ hm).1⟩

end Loc

set_option maxHeartbeats 1000000 in

theorem rows_mass_genus : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (Fm : LocFam (zOf Y) Cl (NuC D)), Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' → ClsRow TS cls → LocClosed F F' (zOf Y) Fm.FP TS → (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) → (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = toPts w → OverOrb Fm t p (Fm.d0 p)) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P → ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀) → (∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2) → ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × NuC D, Fm.dat x.1 x.2 = some d) → ∀ dd : Dat (zOf Y) Fm.FP, (∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1) → (∀ p, p ∉ Fm.P → dd p = Fm.d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (dd p) τ) ∧ ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) = massA F F' dd := by
  intro D X Y u u' F F' w hZ hG Cl TS cls Fm hB hCR hLC hDs hstd hΛ₀ hdat d hx dd hddP hddN
  have hRG : ∀ p, (Fm.FP p).RelG (Formalism.MainNotions.S.LocNG.theta ((zOf Y).M p)) := fun p =>
    (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w F F' hZ hG p).2 _ ⟨(hB p).1, (hB p).2.1, (hB p).2.2.1, (hB p).2.2.2⟩
  have hMo : ∀ p, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := fun p => rank_Vp p
  have luniq : ∀ p (a b : Formalism.MainNotions.S.LocNG.Datum (Fm.FP p)) (τ τ' : Formalism.MainNotions.S.Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS),
      Formalism.MainNotions.S.LocNG.IsTermOver (Fm.FP p) a τ → Formalism.MainNotions.S.LocNG.IsTermOver (Fm.FP p) b τ' → τ.abelian₂ = τ'.abelian₂ → a = b :=
    fun p a b τ τ' h1 h2 h3 => GlobalTheory.T.hermitianDatum_eq_of_same_lattice _ (hMo p) _ _ _ _ (hrk p) (hRG p) a b τ τ' h1 h2 h3
  have hA : ∀ t ∈ TS, ptPN t = toPts w → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) →
      ∃ (Λ : LV D) (y : Dat (zOf Y) Fm.FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen dd y ∧
        ∀ p a, OverOrb Fm t p a ↔ Formalism.MainNotions.S.LocNG.Datum.Rel a (y p) := by
    intro t ht hpt hov
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.exists_termLattice_baseFrames_of_basePoint D X Y u u' F F' w hZ hG t hpt
    obtain ⟨y, hy, hyr⟩ := GlobalTheory.T.localData_of_term_lattice_and_orbits D X Y u u' F F' w hZ hG (zOf Y) Fm.FP hB hRG t Λ hΛ
    have hyr' : ∀ p a, OverOrb Fm t p a ↔ Formalism.MainNotions.S.LocNG.Datum.Rel a (y p) := fun p a => hyr p a
    refine ⟨Λ, y, hΛ, hy, ⟨fun p => ?_, ?_⟩, hyr'⟩
    · by_cases hp : p ∈ Fm.P
      · rw [hddP p hp]; exact (hyr' p _).1 (hov p hp)
      · rw [hddN p hp]; exact (hyr' p _).1 (hstd p hp t ht hpt)
    · obtain ⟨Λ₀, hL0, hτ0⟩ := hΛ₀
      have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D (zOf Y)).1 Λ Λ₀ hy.1 hL0).1
      refine ((Fm.P.finite_toSet).union hfin).subset ?_
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      by_contra hno
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hno
      obtain ⟨hpP, hlat⟩ := hno
      obtain ⟨τ0, hτ0o, hτ0l⟩ := hτ0 p hpP
      obtain ⟨τ, hτo, hτl⟩ := hy.2 p
      apply hp
      rw [hddN p hpP]
      exact (luniq p _ _ _ _ hτ0o hτo (by rw [hτ0l, hτl, hlat])).symm
  obtain ⟨x0, hx0⟩ := hx
  obtain ⟨⟨t0, ht0, hc0, hpt0, hn0⟩, hall0⟩ := (hdat x0.1 x0.2).2 d hx0
  obtain ⟨Λ, y, hΛ, hy, hgen, -⟩ := hA t0 ht0 hpt0 (hall0 t0 ht0 hc0 hpt0 hn0).1
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨τ, hτ, -⟩ := hy.2 p
    exact term_of_rel (hMo p) (hrk p) (hRG p) (rel_symm (hMo p) (hrk p) (hRG p) (hgen.1 p)) ⟨τ, hτ⟩
  have hkey_wt : ∀ t t' : TauC Y u u', key t = key t' →
      Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' := by
    intro t t' h
    have h1 : t.lam = t'.lam := congrArg (fun k => k.1.1.1) h
    have h2 : t.lam' = t'.lam' := congrArg (fun k => k.1.2.1.1) h
    unfold Formalism.L2.SG.TermOp.wt
    rw [h1, h2]
  let K : Set _ := {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat (zOf Y) Fm.FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen dd y ∧
    key t = κ}
  have hKmem : ∀ κ ∈ K, ∃ t : TauC Y u u', key t = κ := by
    rintro κ ⟨t, -, -, -, -, -, -, h⟩
    exact ⟨t, h⟩
  let ω : K → ℝ := fun κ => Formalism.L2.SG.TermOp.wt (Classical.choose (hKmem κ.1 κ.2)) ^ 2
  have hω : ∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = Formalism.L2.SG.TermOp.wt t ^ 2 := by
    intro κ t ht
    show Formalism.L2.SG.TermOp.wt (Classical.choose (hKmem κ.1 κ.2)) ^ 2 = _
    rw [hkey_wt _ _ ((Classical.choose_spec (hKmem κ.1 κ.2)).trans ht.symm)]
  have hsum := GlobalTheory.T.unfolding_genus_weights_sum_to_mass D X Y u u' F F' w hZ hG (zOf Y) Fm.FP hB hRG TS hLC t0 Λ y dd ht0 hΛ hy hgen K rfl ω hω
  rw [← hsum]
  have hsel : ∀ x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d},
      ∃ t ∈ TS, cls t = x.1.1 ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = x.1.2 :=
    fun x => ((hdat x.1.1 x.1.2).2 d x.2).1
  let tx : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d} → TauC Y u u' := fun x => Classical.choose (hsel x)
  have htx : ∀ x, tx x ∈ TS ∧ cls (tx x) = x.1.1 ∧ ptPN (tx x) = toPts w ∧ nmlOf Y u u' (tx x) = x.1.2 :=
    fun x => Classical.choose_spec (hsel x)
  have hmemK : ∀ x, key (tx x) ∈ K := by
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := htx x
    obtain ⟨Λx, yx, hΛx, hyx, hgx, -⟩ := hA (tx x) h1 h3 ((((hdat x.1.1 x.1.2).2 d x.2).2 (tx x) h1 h2 h3 h4).1)
    exact ⟨tx x, h1, Λx, yx, hΛx, hyx, hgx, rfl⟩
  let f : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d} → K := fun x => ⟨key (tx x), hmemK x⟩
  have hinj : Function.Injective f := by
    intro x1 x2 h
    have hk : key (tx x1) = key (tx x2) := congrArg Subtype.val h
    have hn : nmlOf Y u u' (tx x1) = nmlOf Y u u' (tx x2) := congrArg Prod.snd hk
    have hr : (Y.tO u u').rowOf (tx x1) = (Y.tO u u').rowOf (tx x2) := congrArg Prod.fst hk
    obtain ⟨a1, b1, -, d1⟩ := htx x1
    obtain ⟨a2, b2, -, d2⟩ := htx x2
    have hc := (hCR _ a1 _ a2 hn).2 hr
    apply Subtype.ext
    apply Prod.ext
    · rw [← b1, ← b2, hc]
    · rw [← d1, ← d2, hn]
  have hsurj : Function.Surjective f := by
    rintro ⟨κ, hκ⟩
    obtain ⟨t, ht, Λt, yt, hΛt, hyt0, hgt0, hkt⟩ := hκ
    have hyt : LocOver Λt yt := hyt0
    have hgt : InGen dd yt := hgt0
    subst hkt
    have hpt := (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hZ hG t Λt hΛt).2
    cases hdc : Fm.dat (cls t) (nmlOf Y u u' t) with
    | none =>
      exact absurd ⟨t, ht, rfl, hpt, rfl⟩ ((hdat (cls t) (nmlOf Y u u' t)).1 hdc)
    | some d' =>
      have hall := ((hdat (cls t) (nmlOf Y u u' t)).2 d' hdc).2 t ht rfl hpt rfl
      obtain ⟨y', hy', hyr'⟩ := GlobalTheory.T.localData_of_term_lattice_and_orbits D X Y u u' F F' w hZ hG (zOf Y) Fm.FP hB hRG t Λt hΛt
      have hd' : d' = d := by
        funext p
        apply Subtype.ext
        have e1 : Formalism.MainNotions.S.LocNG.Datum.Rel (d' p).1 (y' p.1) := (hyr' p.1 _).1 (hall.1 p.1 p.2)
        have eyy : y' p.1 = yt p.1 := by
          obtain ⟨τ, hτ, hτl⟩ := hy'.2 p.1
          obtain ⟨τ', hτ', hτl'⟩ := hyt.2 p.1
          exact luniq _ _ _ _ _ hτ hτ' (hτl.trans hτl'.symm)
        have e2 : Formalism.MainNotions.S.LocNG.Datum.Rel (d p).1 (yt p.1) := by
          have h := hgt.1 p.1
          rw [hddP p.1 p.2] at h
          exact h
        rw [eyy] at e1
        exact eq_of_rel_reps (hMo p.1) (hrk p.1) (hRG p.1) (Fm.R p.1) (hDs p.1 p.2 _ (d' p).2)
          (hDs p.1 p.2 _ (d p).2) e1 e2
      rw [hd'] at hdc
      refine ⟨⟨(cls t, nmlOf Y u u' t), hdc⟩, ?_⟩
      apply Subtype.ext
      obtain ⟨h1, h2, -, h4⟩ := htx ⟨(cls t, nmlOf Y u u' t), hdc⟩
      have hrow := (hCR _ h1 t ht h4).1 h2
      show key (tx ⟨(cls t, nmlOf Y u u' t), hdc⟩) = key t
      unfold key
      rw [hrow, h4]
  calc ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1)
      = ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (ω (f x)) := by
        refine tsum_congr fun x => ?_
        obtain ⟨h1, h2, h3, h4⟩ := htx x
        rw [hω (f x) (tx x) rfl, (((hdat x.1.1 x.1.2).2 d x.2).2 (tx x) h1 h2 h3 h4).2]
    _ = ∑' κ : K, ENNReal.ofReal (ω κ) :=
        (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq (fun κ => ENNReal.ofReal (ω κ))

end GlobalTheory.Unfold.GenusRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubgroupHaarEqConstSmulPiLocalMeasures
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.MuHPi

theorem hloc_eq_HGv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.Pf.WuDec.Hloc X u v =
      (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) := by
  rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]
  rfl

theorem muH_eq_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muHl C u (X.pl v) v) (Formalism.L2.SG.Pf.WuDec.Hloc X u v) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muHl C u τ w) (Formalism.L2.SG.Pf.WuDec.Hloc X u w) := by
      rintro τ _ rfl; exact invOn_muHl C u τ
    intro v
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_coe] at hc hi
  refine Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG X u)
    (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG, Subgroup.coe_pi]
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_conc _ _ fun v => by rw [← hloc_eq_HGv]; exact (hloc v).2.2.1
  · intro g hg
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v)
      (by rw [hloc_eq_HGv]; exact hg v (Set.mem_univ v))
  · exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuHPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstSmulPiLocalMeasures
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory.MuNPi

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem muN_eq_pi_muNl : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muNl C (X.pl v) v) (NGv X u v : Set _) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muNl C τ w) (NGv X u w : Set _) := by
      rintro τ _ rfl
      exact invOn_muNl C u τ
    exact fun v => h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muNl C (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  rw [← NinfG_coe] at hc hi
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [NinfG, Subgroup.coe_pi]
    exact PiM.pi_conc _ _ fun v => (hloc v).2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · exact PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuNPi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupHaarProductEqPiLocalImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section
namespace GlobalTheory.MuSPi

theorem muNH_prod_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  intro D X θ C u κN κH hN hH
  have hsN : ∀ v, SigmaFinite (muNl C (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ _ rfl; exact sf_muNl C τ (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ)
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsH : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsM : ∀ v, SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl; exact (invOn_mulMap C u τ).1
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  congr 1
  have mp := Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurePreserving_piProd (fun v => muNl C (X.pl v) v) (fun v => muHl C u (X.pl v) v)
  rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
    mp.measurable]
  haveI : ∀ v, SigmaFinite (((muNl C (X.pl v) v).prod (muHl C u (X.pl v) v)).map
      (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hsM
  exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
    (fun v => measurable_mul.aemeasurable)

end GlobalTheory.MuSPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselNormSqBruhatProduct
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem weil_bruhatProd_normSq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (κ : ℝ≥0∞) (M : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (M v)) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = κ • Measure.pi M → ∀ (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞), (∀ v, Measurable (β v)) → (∀ v x, ∫⁻ s, β v (s * x) ∂(M v) = 1) → ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = κ := by
  intro D X u κ M hMs hS β hβm hβ1
  haveI := hMs
  obtain ⟨hNsf, -, hN0, -⟩ := X.muN_haar u
  obtain ⟨hHsf, -, hH0, -⟩ := X.muH_haar u
  haveI := hNsf
  haveI := hHsf
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  have hSmeas : MeasurableSet (X.SinfU u) := (Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u).measurableSet
  have hae : ∀ᵐ s ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)), s ∈ X.SinfU u := by
    refine (ae_map_iff (p := fun s => s ∈ X.SinfU u) hmul.aemeasurable hSmeas).2 ?_
    have h1 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun s => s ∈ X.NinfU u) (by rw [ae_iff]; exact hN0)
    have h2 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun s => s ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}))
        (by rw [ae_iff]; exact hH0)
    filter_upwards [h1, h2] with p hp1 hp2
    exact Formalism.L2.SG.WuDecayPf.mul_mem_sinfU X u p.1 p.2 hp1 hp2
  have hβprod : Measurable (fun x : X.B.I.Ginf => ∏ v, β v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hβm v).comp (measurable_pi_apply v)
  have hWm : Measurable (fun x : X.B.I.Ginf => ‖X.Wu u x‖ₑ ^ 2) :=
    (X.Wu_spec u).2.2.1.enorm.measurable.pow_const 2
  have hfm : Measurable (fun x : X.B.I.Ginf => (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2) := hβprod.mul hWm
  rw [X.nuQ_weil u _ hfm]
  have hin : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
      ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) = κ * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    have e1 : ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
        ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
        ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u x‖ₑ ^ 2
          ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with s hs
      rw [← enorm_norm (X.Wu u (s * x)), Formalism.L2.SG.Pf.WuDec.norm_Wu_inv X u s hs x, enorm_norm]
    rw [e1, lintegral_mul_const _ (show Measurable (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) from
      hβprod.comp (measurable_mul_const x)), hS, lintegral_smul_measure]
    have e2 : ∫⁻ s, ∏ v, β v ((s * x) v) ∂(Measure.pi M) = 1 := by
      have e3 : (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) = fun s => ∏ v, β v (s v * x v) := rfl
      rw [e3, QPK.lintegral_fintype_prod (fun v s => β v (s * x v))
        (fun v => (hβm v).comp (measurable_mul_const _))]
      simp [hβ1]
    rw [e2, smul_eq_mul, mul_one]
  simp only [hin]
  rw [lintegral_const_mul _ hWm, (X.Wu_spec u).2.2.2.2, mul_one]

end GlobalTheory
end

