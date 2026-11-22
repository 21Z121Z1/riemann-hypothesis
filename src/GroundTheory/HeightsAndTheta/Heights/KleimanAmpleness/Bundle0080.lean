import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0071
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockGenDiagLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def BlockGen (S : Type*) [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  ∀ j : ι k₀, y ⟨k₀, j⟩ ≠ 0 → ∀ k, ∃ w : ι k → Ω,
    (∀ a b, y ⟨k, a⟩ * w b ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j)) ∧
      ∑ b, y ⟨k, b⟩ * w b = 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

section Points

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem exists_locIn_of_eq {A B : Subalgebra F Ω} (hAB : A = B) (p : Ideal A) (hp : p.IsPrime) :
    ∃ q : Ideal B, q.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn A p = IndefiniteRowSideFullHecke.Kleiman2.locIn B q := by
  subst hAB
  exact ⟨p, hp, rfl⟩

theorem chartRingOver_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) (c : Unit → κ') :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) c =
      chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) (fun u => σ (c u)) := by
  rw [SectionsOverLocalization.chartRingOver_oneBlock_eq, SectionsOverLocalization.chartRingOver_oneBlock_eq]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩

variable (F) in

theorem modelPts_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) := by
  ext z
  constructor
  · rintro ⟨c, hc, p, hp, rfl⟩
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq (chartRingOver_oneBlock_comp σ v c) p hp
    exact ⟨fun u => σ (c u), fun u => hc u, q, hq, he⟩
  · rintro ⟨c, hc, p, hp, rfl⟩
    have hc' : ∀ u, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ) ⟨u, σ.symm (c u)⟩ ≠ 0 := fun u => by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.oneBlock] using hc u
    have hch : chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) c =
        chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) (fun u => σ.symm (c u)) := by
      rw [chartRingOver_oneBlock_comp σ v]
      simp
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq hch p hp
    exact ⟨fun u => σ.symm (c u), hc', q, hq, he⟩

variable (F) in

theorem modelPts_eq_of_base {N : ℕ} {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K)
    (e : ι k₀ ≃ Fin (N + 1)) {K' : Type} {ι' : K' → Type} (y' : (Σ k, ι' k) → Ω) (k₀' : K')
    (e' : ι' k₀' ≃ Fin (N + 1)) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀)
    (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = IndefiniteRowSideFullHecke.Kleiman2.modelPts F y' := by
  rw [hy.2, hy'.2, ← modelPts_oneBlock_comp F e.symm, hx, modelPts_oneBlock_comp F e'.symm]

end Points

theorem veryAmple_change (hGen : ModelChangeGen.Statement) (F : Type) [Field F] (Ω : Type) [Field Ω]
    [Algebra F Ω] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1))
    (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm)
    (β : K → ℤ) (β' : K' → ℤ)
    (hs : ∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) :
    IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β' := by
  have h0 : secOver F y β = secOver F y' β' := by simpa using hs 0
  have hpts := modelPts_eq_of_base F y k₀ e y' k₀' e' hy hy' hx
  unfold IndefiniteRowSideFullHecke.Kleiman2.VeryAmple IndefiniteRowSideFullHecke.Kleiman2.SameModel
  rw [hpts]
  constructor
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    refine ⟨n, x', fun j => h0 ▸ hmem j, ?_, hsame⟩
    exact (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem).1 hgen
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    have hmem' : ∀ j, x' j ∈ secOver F y β := fun j => h0 ▸ hmem j
    exact ⟨n, x', hmem', (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem').2 hgen, hsame⟩

theorem VeryAmpleModel.proof (hVA : VeryAmpleEq.Statement) (hGen : ModelChangeGen.Statement) :
    VeryAmpleModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hxe hmod Q β hQ
  subst hxe
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (Q.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen Q n g := hg
  have hmod' := GraphModel.full F N Ω _ Q n (r + 1) g hx hgen
  have hsec := realises_graph Q n g hgen
  rw [hVA F N Ω _ Q n (r + 1) g hgen]
  exact (veryAmple_change hGen F Ω N K ι y k₀ e (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock
    (Equiv.refl _) hmod hmod' rfl β (graphDeg n) (fun c => (hQ c).symm.trans (hsec c))).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)

theorem RealiseRestrict.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement)
    (hR : ResidueMap.Statement) (hRG : ResidueGen.Statement) (hC : RestrictGen.Statement) :
    RealiseRestrict.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy Q β hQ K' _ _ y' hy' hI hxy
  subst hx
  obtain ⟨Q'', hQ''⟩ := BundleOfDeg.full F K ι K' y' k₀ N e hy' β
  obtain ⟨ca, hca⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨cb, hcb⟩ := Kleiman.Generated.full F K' N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) Q''
  obtain ⟨cg, hcg⟩ := hG F K ι Ω y k₀ hy β
  obtain ⟨c, hcA, hcB, hcG⟩ : ∃ c, ca ≤ c ∧ cb ≤ c ∧ cg ≤ c :=
    ⟨max ca (max cb cg), by omega, by omega, by omega⟩
  obtain ⟨R, σ, hfr, hblk, hch⟩ := hR F K ι Ω y K' y' hI
  choose d₀ hd₀ using hy'.1
  obtain ⟨ρ, hρ1, hρ2⟩ := hRG F K ι Ω y K' y' hI R σ hfr hch (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (hcg c hcG) d₀ hd₀

  have hT : ∀ t : K', t ∈ secOver F y' (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm),
        t ∈ Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
          (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := by
    intro t
    have h := hS F K ι K' y' k₀ N e _ rfl hy' (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) 0 t
    simp only [PowRealises.twistMod_zero, mul_one, Submodule.mem_iInf, Submodule.restrictScalars_mem,
      neg_zero, zpow_zero] at h
    rw [h, PowRealises.mem_secOver]
    refine forall_congr' fun cc => forall_congr' fun hc => ?_
    rw [hρ2 cc hc, PowRealises.mem_span_inv_iff _
      (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))]
  have hQgen : ∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
        (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := fun I => by
    rw [← hca c hcA I, hQ c]
  have hQ''gen : ∀ I, (Q''.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
        (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := fun I => by
    rw [← hcb c hcB I, hQ'' c]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hT t).mp ht I
    · rw [Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ((hT t).mpr fun J => Submodule.subset_span ht)

  have hfx : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
      aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g ≠ 0 →
      ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g ∈ R,
        σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) f /
          aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g := by
    intro f g m hf hg hg0
    obtain ⟨h, hh⟩ := hblk k₀ (rename e.symm f) (rename e.symm g) m hf.rename_isHomogeneous
      hg.rename_isHomogeneous (by rwa [aeval_rename])
    have ea : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm f) /
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm g) =
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g := by
      rw [aeval_rename, aeval_rename]
    refine ⟨ea ▸ h, ?_⟩
    have hsub : (⟨_, ea ▸ h⟩ : R) = ⟨_, h⟩ := Subtype.ext ea.symm
    rw [hsub, hh, aeval_rename, aeval_rename]
  have hw' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  obtain ⟨r, hr⟩ := hC F N Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) K' (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) hxy
    R σ hfx Q Q'' c (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ρ
    (∏ k, y ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k))
    (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) hw' hQgen hQ''gen hρ1
  exact ⟨Q'', r, hr, hQ''⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ChartKernel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (Ω : Type) [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (Ω' : Type) [Field Ω'] [Algebra S Ω'] (y' : (Σ k, ι k) → Ω'),
    mIdealOver S y ≤ mIdealOver S y' → ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∀ g : MvPolynomial (Σ k, ι k) S, aeval (fun p => y p / y ⟨p.1, c p.1⟩) g = 0 →
        aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleTwistVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

theorem twistVanishAll_closed : Kleiman.TwistVanishAll.Statement.{0, 0} :=
  Kleiman.TwistVanishAll.proof Kleiman.Extension.full Kleiman.SerreVanish.full Kleiman.TwistSplit.proof

theorem lineBundle_twist_vanish {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (Q : Kleiman.LineBundle F x) :
    ∃ c₀ : ℤ, ∀ (i : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton ((Q.twist (Kleiman.twistSys F x c)).H i) := by
  obtain ⟨c₀, hc₀⟩ := twistVanishAll_closed F Ω N x Q (Kleiman.twistBundle F x 1) N x
    Kleiman.mem_secs_twistBundle_one Kleiman.span_range_eq_twistMod_one
  refine ⟨c₀, fun i c hi hc => ?_⟩
  have h := hc₀ i 0 c hi hc
  have e : Q.twist ((Kleiman.twistBundle F x 1).pow 0) = Q.toSubSystem :=
    Kleiman.SubSystem.twist_twistSys_zero _
  rwa [e] at h

theorem RayVanish.proof (hMC : ModelCechTwist.Statement) : RayVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ hM β
  have : Nonempty (ι k₀) := let ⟨i, _⟩ := hM.1 k₀; ⟨i⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := lineBundle_twist_vanish Q
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun c hc i hi => ?_⟩
  obtain ⟨φ⟩ := hMC F K ι Ω y k₀ N e hM β Q hQ 1 1 0 c i
  have hdeg : (1 : ℕ) • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β 1 0 + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ =
      β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL]
  have hsys : (Kleiman.twistMul Q.toSubSystem 1 0).pow 1 = Q.toSubSystem := by
    change (Kleiman.twistSys _ _ 0).twist (Kleiman.twistMul Q.toSubSystem 1 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.twistMul]
    change ((Kleiman.twistSys _ _ 0).twist Q.toSubSystem).twist (Kleiman.twistSys _ _ 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.SubSystem.twist_twistSys_zero]
  rw [hdeg, hsys] at φ
  have := hc₀ i c hi (by omega)
  exact φ.symm.toEquiv.subsingleton

theorem RayVanish.proof_of_ties (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) :
    RayVanish.Statement :=
  RayVanish.proof (ModelCechTwist.proof (ChartSecMul.proof BundleOfDeg.full) BaseRealises.proof hLoc hRef)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MIdealOverOneHeightslock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

section Block

variable {F : Type} [Field F] {K : Type} {ι : K → Type} {L : Type} [Field L] [Algebra F L]

theorem comap_mIdealOver_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    (mIdealOver F y).comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) := by
  have h1 : (mConeMapOver F y).comp (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      ((Polynomial.aeval (X k₀ : MvPolynomial K L)).restrictScalars F).comp
        (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have h2 : ∀ q : Polynomial L,
      aeval (fun _ : K => (Polynomial.X : Polynomial L)) (Polynomial.aeval (X k₀ : MvPolynomial K L) q) = q :=
    fun q => by rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver F y (rename _ f) = 0 ↔ _
  have h := AlgHom.congr_fun h1 f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [← h2 (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

theorem mIdealOver_oneBlock_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      baseComap F k₀ e (mIdealOver F y) := by
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := L) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  ext f
  rw [baseComap, Ideal.mem_comap]
  change mConeMapOver F _ f = 0 ↔ mConeMapOver F y (rename _ f) = 0
  have h := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact rename_injective _ (fun a b _ => Subsingleton.elim a b) (h0.trans (map_zero _).symm)

end Block

theorem CurveNumModel.proof (hMP : ModelPoint.Statement) (hRR : RealiseRestrict.Statement)
    (hIR : Kleiman.InterNumRestrict.Statement.{0, 0}) (hNM : NumModel.Statement) (hMC : ModelCurves.Statement) :
    CurveNumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hm Q β hQ W hW hle hrel
  classical
  have := hW.isPrime
  have hWy : mIdealOver F (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := F), hWy]
  have hy' : ∀ k, ∃ i, genPtOf W ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hW.relevant k
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hleW : mIdealOver F y ≤ mIdealOver F (genPtOf W) := hWy.symm ▸ hle
  have hm' := hMP F K ι Ω y k₀ hm _ (genPtOf W) hy' hleW
  have hxy : ∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0 := fun i h h0 => by
    rw [hx] at h0
    exact h ((hzero ⟨k₀, e.symm i⟩).mpr (hle ((X_mem_mIdealOver_iff y ⟨k₀, e.symm i⟩).mpr h0)))
  obtain ⟨Q', r, hR, hQ'⟩ := hRR F K ι Ω y k₀ N e x hx hm Q β hQ _ (genPtOf W) hm' hleW hxy
  have hpp : Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) =
      W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) := by
    rw [← comap_mIdealOver_block, hWy]
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)) 1 := by
    refine (isSubvar_iff_relDim _ 1).mpr ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hy' k₀
      exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
    · rw [mIdealOver_oneBlock_block, hWy]
      exact ((hMC F K ι Ω y k₀ N e x hx hm 1).1 W hW hle hrel).2.2
  have hxx : Kleiman.primeOf (S := F) x ≤
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) := by
    rw [hx, ← comap_mIdealOver_block, ← comap_mIdealOver_block]
    exact Ideal.comap_mono hleW
  have h1 := hIR F Ω N x _ _ hxy hxx _ 1 hsub ![Q] ![Q'] (fun _ => r) (fun i => by fin_cases i; exact hR)
  have h2 := hNM F K ι _ (genPtOf W) k₀ N e _ rfl hm' 1 ![Q'] ![β] (fun i => by fin_cases i; exact hQ') hsub
  rw [hWy] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1, hpp]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfModelMulSecs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelTwistMulSecs.of_modelMulSecs (h : ModelMulSecs.Statement) : ModelTwistMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p m => h F K ι Ω y k₀ N e hmod β Q hQ p m

theorem ModelTwistMulSecs.proof (hT : TensorRealises.Statement) : ModelTwistMulSecs.Statement :=
  ModelTwistMulSecs.of_modelMulSecs (ModelMulSecs.proof hT BaseRealises.proof)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistMulTwistTwistSys
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem twistMul_twist_twistSys {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a : ℕ) (m c : ℤ) :
    (twistMul M a m).twist (twistSys S x c) = twistMul M a (m + c) := by
  rw [twistMul, twistMul, SubSystem.twist_assoc, twistSys_twist_eq_add]

theorem ModelVeryAmpleEq.proof (hVA : VeryAmpleEq.Statement) (hMS : ModelMulSecs.Statement)
    (hCh : ModelChangeVeryAmple.Statement) : ModelVeryAmpleEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ a m _
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul Q a m
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (L.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen L n g := hg
  have hmod' := GraphModel.full F N Ω _ L n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver L n g hgen
  have hH : ∀ c : ℤ, (L.twist (twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro c
    rw [hL, twistMul_twist_twistSys, hMS F K ι Ω y k₀ N e hmod β Q hQ a (m + c), add_smul, add_assoc]
  rw [← hL, hVA F N Ω _ L n (r + 1) g hgen]
  exact hCh F Ω N (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) K ι y k₀ e hmod' hmod rfl
    (graphDeg n) (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (fun c => (hsec c).symm.trans (hH c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

