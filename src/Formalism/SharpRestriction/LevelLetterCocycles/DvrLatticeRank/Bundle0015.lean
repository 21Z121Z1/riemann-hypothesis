import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0012
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0002

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAlpha
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_φD_smul (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem framepf_smulLA_tmul (π' : LetA O n) (c : ZMod n) (a : LetA O n) (e : W.EE)
    (ℓ : LcQ W T π' c) : smulLA W T π' c a (e ⊗ₜ ℓ) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ ℓ := rfl

theorem framepf_toLA_tmul (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ)
    (s : ↥S) : toLA W T π' c S (a ⊗ₜ s) =
      algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := rfl

variable (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_ι_Δ (i : ZMod n) (g : PowerSeries O) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γA δ (framepf_ι π' i g) = framepf_ι π' i g := by
  have h := framepf_ι_letγ π' i (hπ0 i) (W.γ₀ δ) (γ0 δ hδ) PowerSeries.X (by simp)
    (by rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i))];
        exact congrFun (hΔπ δ hδ) i) g
  rw [PowerSeries.X_subst] at h
  exact h

include hπ0 hΔπ γ0 in
theorem framepf_vec_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' (c - 1) H k ∈ NcS W T (c - 1) := by
  unfold framepf_vec
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [mem_NcS]
  obtain ⟨hN, hΔ⟩ := Bs.mem m
  refine ⟨(W.N T).smul_mem _ hN, fun δ hδ => ?_, ?_⟩
  · rw [gradNPf_γD_smul, framepf_ι_Δ π' hπ0 hΔπ γ0 _ _ δ hδ, hΔ δ hδ]
  · rw [smul_smul, framepf_letE_ι π' (c - 1) hπ0]

include hπ0 hΔπ γ0 in
theorem framepf_hh_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈ NcS W T (c - 1) := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (framepf_vec_mem Bs π' c hπ0 hΔπ γ0 H k)

def framepf_Ψα (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T :=
  LinearMap.liftBaseChange W.EE ((W.φD T).comp (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H))

theorem framepf_Ψα_tmul (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (e : W.EE) (ℓ : LcQ W T π' c) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (e ⊗ₜ ℓ) =
      e • W.φD T (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) := by
  unfold framepf_Ψα
  rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply]

theorem framepf_Ψα_smulLA (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (a : LetA O n)
    (x : W.EE ⊗[O] LcQ W T π' c) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (smulLA W T π' c a x) =
      a • framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ =>
    rw [framepf_smulLA_tmul, framepf_Ψα_tmul, framepf_Ψα_tmul, mul_smul, algebraMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

include hπ0 hΔπ γ0 in

theorem framepf_Ψα_toLA (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c))) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (toLA W T π' c ⊤ t) ∈ PcS W T c := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a s =>
    rw [framepf_toLA_tmul, framepf_Ψα_tmul, algebraMap_smul]
    have hh := framepf_hh_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H (s : LcQ W T π' c)
    rw [mem_NcS] at hh
    obtain ⟨hN, hΔ, hl⟩ := hh
    unfold PcS
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      rw [← hl]
      exact ⟨_, hN, rfl⟩
    · rw [mem_DelS]
      intro δ hδ
      rw [gradNPf_γD_smul, map_mul, ← W.φγ_comm, hΔ δ hδ, a.2 δ hδ, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
    · rw [mem_letS, smul_smul, ← mul_assoc]
      unfold letE
      rw [← Pi.single_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

variable (Eπ : LetA O n) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hEΔ : ∀ δ ∈ W.DelF, W.γA δ Eπ = Eπ) (h' M : ℕ)

include hEu hEΔ in

theorem framepf_Lam_cancel {y : W.DD T} (hΔ : ∀ δ ∈ W.DelF, W.γD T δ (Eπ ^ h' • y) = Eπ ^ h' • y)
    (hl : (letE c : LetA O n) • (Eπ ^ h' • y) = Eπ ^ h' • y) :
    (∀ δ ∈ W.DelF, W.γD T δ y = y) ∧ (letE c : LetA O n) • y = y := by
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
  refine ⟨fun δ hδ => ?_, ?_⟩
  · rw [← sub_eq_zero]
    apply gradNPf_tf W T _ hu'
    have h1 := hΔ δ hδ
    rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ] at h1
    rw [smul_sub, h1, sub_self]
  · rw [← sub_eq_zero]
    apply gradNPf_tf W T _ hu'
    rw [smul_sub, smul_smul, mul_comm, ← smul_smul, hl, sub_self]

include hπ0 hΔπ γ0 hEu hEΔ in

theorem framepf_Ψα_Lam (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (x : W.EE ⊗[O] LcQ W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x ∈ LamPS W T Eπ h' c := by
  obtain ⟨t, ht⟩ := Submodule.mem_comap.1 hx
  have hP := framepf_Ψα_toLA Bs π' c hπ0 hΔπ hR2 γ0 hu H t
  rw [ht, framepf_Ψα_smulLA] at hP
  unfold PcS at hP
  obtain ⟨hP12, hP3⟩ := Submodule.mem_inf.1 hP
  obtain ⟨hP1, hP2⟩ := Submodule.mem_inf.1 hP12
  rw [mem_DelS] at hP2
  rw [mem_letS] at hP3
  rw [Submodule.restrictScalars_mem] at hP1
  obtain ⟨hΔ, hl⟩ := framepf_Lam_cancel c Eπ hEu hEΔ h' hP2 hP3
  rw [mem_LamPS]
  exact ⟨hP1, hΔ, hl⟩

def framepf_α (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    ↥(LamLA W T π' Eπ h' c ⊤) →ₗ[O] QLamP W T π' Eπ h' M c :=
  (Submodule.mkQ _).comp (LinearMap.codRestrict (LamPS W T Eπ h' c)
    (((framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H).restrictScalars O).comp (LamLA W T π' Eπ h' c ⊤).subtype)
    (fun x => framepf_Ψα_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ hEu hEΔ h' H x x.2))

theorem framepf_α_apply (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (x : W.EE ⊗[O] LcQ W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    framepf_α Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ hEu hEΔ h' M H ⟨x, hx⟩ =
      mkP W T π' Eπ h' M c (framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x)
        (framepf_Ψα_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ hEu hEΔ h' H x hx) := rfl

include hπ0 hΔπ γ0 in

theorem framepf_Ψα_J (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (x : W.EE ⊗[O] LcQ W T π' c)
    (hx : x ∈ JLA W T π' Eπ h' M c) :
    framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x ∈ JP W T π' Eπ h' M c := by
  obtain ⟨z, ⟨t, rfl⟩, rfl⟩ := Submodule.mem_map.1 hx
  rw [framepf_Ψα_smulLA]
  exact Submodule.mem_map.2 ⟨_, framepf_Ψα_toLA Bs π' c hπ0 hΔπ hR2 γ0 hu H t, rfl⟩

include hπ0 hΔπ γ0 in

theorem framepf_α_J (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (x : W.EE ⊗[O] LcQ W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hJ : x ∈ JLA W T π' Eπ h' M c) :
    framepf_α Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ hEu hEΔ h' M H ⟨x, hx⟩ = 0 := by
  rw [framepf_α_apply]
  unfold mkP
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  exact framepf_Ψα_J Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ h' M H x hJ

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfD
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem alpha_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hxS : x ∈ NLset W T Pt π' Eπ h' c)
    (y0 : W.DD T) (hy0 : y0 ∈ LamPS W T Eπ h' c) (hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0) :
    y0 ∈ W.N T := by
  obtain ⟨h1, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
  have hE2 : Eπ ^ h' • (Eπ ^ h' • y0) ∈ W.N T := Eπ_φspan W T Eπ h' c hww hQ h5a h1
  have eEQ : Eπ ^ h' = w' ^ h' * W.Q ^ h' := by
    rw [hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]
  refine hexp c y0 ((mem_DelS W T y0).2 h2) ((mem_letS W T c y0).2 h3) ⟨2 * h', ?_⟩ ?_
  · rw [hQ, mul_pow, mul_smul, show Eπ ^ (2 * h') = Eπ ^ h' * Eπ ^ h' by rw [two_mul, pow_add],
      mul_smul]
    exact Submodule.smul_mem _ _ hE2
  · intro ζ τ hPt k hk i
    obtain ⟨hc0, hc1⟩ := levQ_pt W hs c ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
    obtain ⟨m, a, z, hrep, hfil⟩ := hxS
    have e1 : W.Q ^ k • (Eπ ^ h' • y0) = (w' ^ h' * W.Q ^ h') • (W.Q ^ k • y0) := by
      rw [eEQ, smul_smul, smul_smul, mul_comm (W.Q ^ k)]
    have hQΛ : W.Q ^ k • (Eπ ^ h' • y0) ∈ W.N T := e1 ▸ Submodule.smul_mem _ _ hk
    have hF : ∀ i' : ℤ, W.levN T c ζ ⟨_, hQΛ⟩ i' ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) + h' - i') := by
      intro i'
      rcases lt_or_ge i' ((k : ℤ) + 4 * h') with hi | hi
      · rw [(hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx y0 hy0 hα m a z hrep k hQΛ i' hi]
        refine nsmul_mem ?_ _
        have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i))
          (FilC_mono_shift T τ _) (W.lev c ζ (W.Q ^ k)) k
          (by rw [map_pow]; exact pow_vanish' _ hc0 k) _ (hfil τ ζ hPt) i'
        convert this using 2
        ring
      · have h0 := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hQΛ⟩ i')).2
        exact FilC_anti T τ (by omega) (FilC_top T h' τ (hjmp τ) _ h0)
    have hsub : (⟨_, hQΛ⟩ : ↥(W.N T)) = (w' ^ h' * W.Q ^ h') • (⟨_, hk⟩ : ↥(W.N T)) :=
      Subtype.ext e1
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ ⟨_, hk⟩
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
    have hw0 : PowerSeries.constantCoeff (W.lev c ζ w') ≠ 0 := by
      intro h
      have hw : PowerSeries.constantCoeff (W.lev c ζ w') *
          PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
        rw [← map_mul, ← map_mul, hww, map_one, map_one]
      rw [h, zero_mul] at hw
      exact zero_ne_one hw
    have hB0 : PowerSeries.constantCoeff B' ≠ 0 := by
      rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc1
      exact hc1
    have eg : W.lev c ζ (w' ^ h' * W.Q ^ h') =
        PowerSeries.X ^ h' * (W.lev c ζ w' ^ h' * B' ^ h') := by
      rw [map_mul, map_pow, map_pow, hB', mul_pow]
      ring
    refine serMul_inv (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) (FilC_mono_shift T τ _)
      (W.lev c ζ (w' ^ h' * W.Q ^ h')) h' ?_ ?_ (W.levN T c ζ ⟨_, hk⟩) m₀ hm₀ ?_ i
    · intro j hj
      rw [eg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
    · rw [eg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow]
      exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hB0)
    · intro i''
      rw [← levN_eq_serMul, ← hsub]
      have := hF (i'' + h')
      convert this using 2
      ring

end Core

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfC
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem filC_le_bot (τ : K →ₐ[Qp] LL) (h' : ℕ)
    (hJ : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  by_cases ha : -(h' : ℤ) ≤ a
  · exact u3upPf_FilC_anti (PD := PD) T τ ha
  · have hc : ∀ j : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - j) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - (j + 1 : ℕ)) := by
          intro hj
          have := (hJ _ hj).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        push_neg at hnj
        rw [← ih, ← hnj]
        congr 1
        push_cast
        ring
    obtain ⟨j, hj⟩ : ∃ j : ℕ, a = -(h' : ℤ) - j := ⟨(-(h' : ℤ) - a).toNat, by omega⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [hj, hc j]

theorem φD_letter' {i : ZMod n} {x : W.DD T} (hx : (letE (O := O) i : LetA O n) • x = x) :
    (letE (O := O) (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  have hφ : W.φA (letE (O := O) i) = letE (i + 1) := by
    funext j
    simp only [LocWach.φA, letφ]
    by_cases h : j = i + 1
    · subst h
      simp [letE]
    · have h' : j - 1 ≠ i := fun h'' => h (by rw [← h'']; ring)
      simp [letE, h, h']
  rw [← hφ, ← algebraMap_smul W.EE (W.φA (letE i)) (W.φD T x)]
  have h : algebraMap (LetA O n) W.EE (W.φA (letE (O := O) i)) =
      W.φE (algebraMap (LetA O n) W.EE (letE i)) := (W.φE_ext _).symm
  rw [h, ← W.φD_smul, algebraMap_smul, hx]

end Generic

end Formalism.MainNotions.N.Ln34.MLC

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OthDisj
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34
open scoped TensorProduct

section DiscreteGroups

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem oth_disj [CharZero Qp] [FiniteDimensional Qp K] (τ : K →ₐ[Qp] LL) :
    Disjoint (DdRE PD ρ τ) (⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Qp K
  have hint : IsIntegral Qp α := IsIntegral.of_finite Qp α
  have hadj : Algebra.adjoin Qp {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun τ : K →ₐ[Qp] LL => τ α) := by
    intro τ₁ τ₂ h
    have hle := AlgHom.adjoin_le_equalizer τ₁ τ₂ (s := {α}) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h)
    rw [hadj] at hle
    exact AlgHom.ext fun y => hle (Algebra.mem_top (x := y))
  set f : Module.End LL (V ⊗[Qp] BdR) := mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) α
  have hE : ∀ τ' : K →ₐ[Qp] LL, DdRE PD ρ τ' ≤ f.eigenspace (τ' α) := by
    intro τ' x hx
    rw [Module.End.mem_eigenspace_iff]
    have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hx).2 α
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h
    exact h
  have hind := Module.End.eigenspaces_iSupIndep f (τ α)
  refine Disjoint.mono (hE τ) ?_ hind
  refine iSup₂_le fun τ' hτ' => ?_
  exact le_trans (hE τ') (le_iSup₂_of_le (τ' α) (fun h => hτ' (hinj h)) le_rfl)

end DiscreteGroups

section Pt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem dR_le (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    [FiniteDimensional LL ↥(DdRE PD T.ρ τ)] :
    DdRE PD T.ρ τ ≤ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
  obtain ⟨hi, hhi⟩ := fr_fildR_hi PD T.ρ τ
  obtain ⟨lo, hlo⟩ := fr_fildR_lo PD T.ρ τ
  have key : ∀ d : ℕ, FildR PD T.ρ τ (hi - d) ≤
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
    intro d
    induction d with
    | zero =>
      rw [Nat.cast_zero, sub_zero, hhi hi le_rfl]
      exact bot_le
    | succ d ih =>
      intro w hw
      have e1 : -(-(hi - ((d + 1 : ℕ) : ℤ))) = hi - ((d + 1 : ℕ) : ℤ) := neg_neg _
      obtain ⟨x, a, -, -, hx⟩ := (hp4.2 c ζ τ hPt).2.2 (-(hi - ((d + 1 : ℕ) : ℤ))) w (by rwa [e1])
      have e2 : -(-(hi - ((d + 1 : ℕ) : ℤ))) + 1 = hi - (d : ℤ) := by push_cast; ring
      rw [e2] at hx
      have hmem1 : a • W.levN T c ζ ((letE c : LetA O n) • x) (-(hi - ((d + 1 : ℕ) : ℤ))) ∈
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' :=
        Submodule.mem_sup_left (Submodule.smul_mem _ _
          (Submodule.mem_inf.1 ((hp4.2 c ζ τ hPt).2.1 x (-(hi - ((d + 1 : ℕ) : ℤ))))).1)
      have hF : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (hi - (d : ℤ)) ≤
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
        unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
        exact sup_le ih le_sup_right
      have := Submodule.sub_mem _ hmem1 (hF hx)
      rwa [sub_sub_cancel] at this
  have h := key (hi - lo).toNat
  rwa [hlo _ (by omega)] at h

end Pt

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

