import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EWdOfAbove
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigConcrete

theorem wdOfTie {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) : WDOfTie P.T := by
  intro i a r w hl _
  rw [(P.wdOf i a r w).1]
  exact P.wd.away _ _ r w hl

set_option maxHeartbeats 1000000 in

theorem e_wdOf_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D)
    (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ}
    (r : G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (hr : Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))))
    (hd : D.naut.IsdRW i r w) :
    IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (resDec D.nd.plOm.1 r w) ∧
    P.T.e w (D.naut.wdOf i r w) = wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w)
      (D.nbr_ind i w hw) (resDec D.nd.plOm.1 r w) := by
  have hd' : P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w := (P.wdOf i b r w).2.2.2.1.1 hd
  have pst : ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
      (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsPstAt (D.loc (D.nd.l i)) Bw (resDec D.nd.plOm.1 r w) := by
    intro O _ _ _ Bw hj
    exact hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val)
      ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 hd')
  refine ⟨pst _ (D.nbr i w hw) (D.nbr_ind i w hw), ?_⟩
  obtain ⟨L1, B1, j1, e1⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) r w hw
  rw [(P.wdOf i b r w).1, e1]
  exact GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i)
    D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (D.nd.O i) B1 (D.nbr i w hw) j1 (D.nbr_ind i w hw) b _
    (hr.comp continuous_subtype_val) (pst _ B1 j1) (pst _ (D.nbr i w hw) (D.nbr_ind i w hw))

set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    GlobalTheory.LocalInv.EigAway D.nd D.naut P.T.eig ∧ GlobalTheory.LocalInv.EigAbove D.nd D.naut P.T.eig := by
  intro hB hL D P
  refine ⟨eigAway_of_wdOfTie _ _ _ D.nd D.naut P.T (wdOfTie P), ?_⟩
  intro i a ρ χ hρ hχ w hw dρ dχ hs σ hσ
  obtain ⟨p1, e1⟩ := e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) ρ)
    (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i ρ hρ) dρ
  obtain ⟨p2, e2⟩ := e_wdOf_above hB P i w hw (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ))
    (GlobalTheory.LocalInv.cont_mapRep_iotaOQ D.nd D.naut i _ hχ) dχ
  have hW := mem_Weil_of_isFrob (D.nd.plOm.2 w) hσ
  show ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i (GlobalTheory.LocalInv.charRep D.nd i χ) w)).inePol σ).roots ≤
    ((P.T.e w (GlobalTheory.LocalInv.wd D.nd D.naut i ρ w)).inePol σ).roots
  rw [GlobalTheory.LocalInv.wd, GlobalTheory.LocalInv.wd, e1, e2, WD.inePol_of_mem _ hW, WD.inePol_of_mem _ hW]
  obtain ⟨v, hv, hs⟩ := hs
  have hv0 : (D.naut.iotaQ i) ∘ v ≠ 0 := by
    intro h0
    apply hv
    funext k
    have := congrFun h0 k
    simpa using this
  have hM : ∀ g : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)),
      ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) ρ) w g : GL (Fin a) (Om (D.nd.l i))) :
        Matrix (Fin a) (Fin a) (Om (D.nd.l i))) = (GlobalTheory.LocalInv.matK D.nd i ρ g).map (D.naut.iotaQ i) := by
    intro g
    ext p q
    rfl
  have hC : ∀ g : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)),
      ((resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.LocalInv.charRep D.nd i χ)) w g :
        GL (Fin 1) (Om (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Om (D.nd.l i))) 0 0 =
        D.naut.iotaQ i (algebraMap (D.nd.O i) (Kf D.nd i) ((χ g : (D.nd.O i)ˣ) : D.nd.O i)) := by
    intro g
    rfl
  rcases hs with hs | hs
  · refine GlobalTheory.T.local_galois_rep_decomposition_induced (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2
      ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩
    rw [hM, hC]
    funext k
    rw [← RingHom.map_mulVec, hs g g.2]
    simp
  · refine GlobalTheory.T.local_galois_rep_induced_matches (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ (D.naut.iotaQC i) (D.nbr i w hw)
      (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ _ p1 p2 ((D.naut.iotaQ i) ∘ v) hv0 (fun g => ?_) ⟨σ, hW⟩
    rw [hM, hC]
    funext k
    rw [← RingHom.map_vecMul, hs g g.2]
    simp

end GlobalTheory.EigConcrete

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNat
section
open NumberField

open scoped IntermediateField

namespace GlobalTheory.CMSqrtNeg

theorem finrank_adjoin_sq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (c : E) (t : Ω)
    (ht : t ^ 2 = algebraMap E Ω c) (hn : t ∉ Set.range (algebraMap E Ω)) :
    IsIntegral E t ∧ Module.finrank E E⟮t⟯ = 2 := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c two_ne_zero
  have h0 : Polynomial.aeval t (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by simp [ht]
  have hi : IsIntegral E t := ⟨_, hm, by simpa [Polynomial.aeval_def] using h0⟩
  refine ⟨hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  have h1 : (minpoly E t).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd E t h0) hm.ne_zero
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  have h2 : 2 ≤ (minpoly E t).natDegree := (minpoly.two_le_natDegree_iff hi).2 (by simpa using hn)
  omega

theorem exists_qcm_adjoin_sqrt_neg : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) →
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  intro E Ω _ _ _ _ _ _ p hp δ hδ hδn
  have hδ' : δ ^ 2 = algebraMap E Ω (-(p : E)) := by simp [hδ]
  obtain ⟨hint, htwo⟩ := finrank_adjoin_sq (-(p : E)) δ hδ' hδn
  haveI : FiniteDimensional E E⟮δ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField E⟮δ⟯ := NumberField.of_module_finite E _
  obtain ⟨d, s, hs, hsn, hneg⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hs0 : s ≠ 0 := fun h => hsn (h ▸ zero_mem _)
  let t : E⟮δ⟯ := ⟨δ * algebraMap E Ω s,
    mul_mem (IntermediateField.subset_adjoin E {δ} rfl) (IntermediateField.algebraMap_mem _ s)⟩
  let d' : maximalRealSubfield E := -(p : maximalRealSubfield E) * (d : maximalRealSubfield E)
  have ht : t ^ 2 = algebraMap E E⟮δ⟯ (algebraMap (maximalRealSubfield E) E d') := by
    apply Subtype.ext
    show (δ * algebraMap E Ω s) ^ 2 = algebraMap E Ω (algebraMap (maximalRealSubfield E) E d')
    rw [mul_pow, hδ, ← map_pow, hs]
    simp [d']
  have htn : t ∉ Set.range (algebraMap E E⟮δ⟯) := by
    rintro ⟨e, he⟩
    apply hδn
    refine ⟨e * s⁻¹, ?_⟩
    have h1 : algebraMap E Ω e = δ * algebraMap E Ω s := congrArg Subtype.val he
    have h2 : algebraMap E Ω s ≠ 0 := (map_ne_zero _).2 hs0
    rw [map_mul, h1, map_inv₀, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hpos : ∀ φ : maximalRealSubfield E →+* ℝ, 0 < φ d' := fun φ => by
    have := hneg φ
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    simp only [d', map_mul, map_neg, map_natCast]
    nlinarith
  have hcm := (GlobalTheory.isCMField_of_sq_eq_totallyPositive E E⟮δ⟯ htwo d' t ht htn hpos).1
  exact ⟨⟨E⟮δ⟯, nf, hcm, htwo⟩, rfl⟩

end GlobalTheory.CMSqrtNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDoubleCosetCommutingMapPrincipalCongruence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIsoMap

theorem isoMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsoRep S₁ S₂ → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  classical
  intro L _ _ _ n a S₁ S₂ hS₁ hiso N hN hex
  obtain ⟨T, hT⟩ := hiso
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (S₂.subtype ∘ₗ T.toLinearMap)
  have hφS : ∀ f (hf : f ∈ S₁), φ f = ((T ⟨f, hf⟩ : S₂) : GAf L n → a.W) := by
    intro f hf
    have := LinearMap.congr_fun hφ ⟨f, hf⟩
    simpa using this
  have hrt : ∀ h (f : GAf L n → a.W), f ∈ S₁ → φ (NG.rt L n h f) = NG.rt L n h (φ f) := by
    intro h f hf
    have hf' : NG.rt L n h f ∈ S₁ := hS₁.1.stable h f hf
    rw [hφS _ hf', hφS _ hf]
    exact hT h ⟨f, hf⟩ ⟨_, hf'⟩ rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro f hf hfix
    refine ⟨?_, fun κ hκ => ?_⟩
    · rw [hφS _ hf]; exact (T ⟨f, hf⟩).2
    · rw [← hrt κ f hf, hfix κ hκ]
  · obtain ⟨f, hf, hfix, hne⟩ := hex
    refine ⟨f, hf, hfix, ?_⟩
    rw [hφS _ hf]
    intro h0
    apply hne
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff T).1 this)
    simpa using this
  · intro g f hf hfix
    set J := GlobalTheory.IsotOrth.congSub L n N with hJ
    set D : Set (GAf L n) := {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * g * u'} with hD
    obtain ⟨M, hM, hMc⟩ := GlobalTheory.ConjCong.exists_cong_conj L n N g hN
    have hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite := by
      refine ((GlobalTheory.HeckeRecon.finite_cosets (L := L) (n := n) (N * M) (Nat.mul_pos hN hM)).image
        (fun c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M) => ((c.out * g : GAf L n) : GAf L n ⧸ J))).subset ?_
      rintro _ ⟨x, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)), ⟨u, (show NG.Cong L n N u from hu).1, rfl⟩, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k ∈ GlobalTheory.IsotOrth.congSub L n (N * M),
          (Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))) = u * k := by
        have h1 := QuotientGroup.out_eq' (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))
        rw [QuotientGroup.eq] at h1
        exact ⟨_, Subgroup.inv_mem _ h1, by group⟩
      obtain ⟨hkmem, hkeq⟩ := hk
      show ((Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)) * g : GAf L n) : GAf L n ⧸ J) = ((u * g * u' : GAf L n) : GAf L n ⧸ J)
      rw [hkeq, QuotientGroup.eq]
      have hc : g⁻¹ * k * g ∈ J := hMc k hkmem
      have : (u * k * g)⁻¹ * (u * g * u') = (g⁻¹ * k * g)⁻¹ * u' := by group
      rw [this]
      exact J.mul_mem (J.inv_mem hc) hu'
    have hsum : ∀ F : GAf L n → a.W, NG.heckeD J D F = ∑ c ∈ hfin.toFinset,
        (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then NG.rt L n hc.choose F else 0) := by
      intro F
      funext x
      rw [GlobalTheory.HeckeRecon.heckeD_eq_sum J D hfin, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · exact hrt _ f hf
    · exact map_zero φ

end GlobalTheory.HeckeIsoMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section
open Module

namespace GlobalTheory.NormBC

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem isUnit_of_isUnit_norm {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Free B A]
    [Module.Finite B A] {z : A} (h : IsUnit (Algebra.norm B z)) : IsUnit z := by
  rw [Algebra.norm_apply] at h
  have hu : IsUnit (LinearMap.mul B A z) := (LinearMap.isUnit_iff_isUnit_det _).2 h
  obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
  exact IsUnit.of_mul_eq_one y (by simpa using hy)

end GlobalTheory.NormBC

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def toAlg (L : FinExt l) : Bst P ⊗[ℚ_[l]] (Fin 1 → ↥L.1) ≃ₗ[Bst P] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Bst P) (Bst P))
    (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1)

theorem toAlg_comm (L : FinExt l) (z : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toAlg P L (TensorProduct.comm ℚ_[l] (Fin 1 → ↥L.1) (Bst P) z) = toA P L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x x' hx hx' => simp only [map_add, hx, hx']

theorem linearIndependent_toA {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (b : Basis (Fin d) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) :
    LinearIndependent ↥(MaximalUnramifiedExtension l)
      (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
  have h := b.linearIndependent.map' (((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ
    GlobalTheory.PstRank.toB P ρ) (LinearMap.ker_eq_bot.mpr ((toAlg P L).injective.comp (GlobalTheory.PstRank.toB_injective P ρ)))
  have hf : (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) =
      ⇑(((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ GlobalTheory.PstRank.toB P ρ) ∘ ⇑b :=
    funext fun i => (toAlg_comm P L _).symm
  rw [hf]
  exact h

end GlobalTheory.Pst.UnitLetter

namespace GlobalTheory.Pst.UnitLetter

open GlobalTheory.NormBC

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_common_fixed {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (hy : ∀ i, y i ∈ Dpst P ρ) :
    ∃ K' : FinExt l, ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' → stRep P ρ g (y i) = y i := by
  suffices h : ∀ s : Finset (Fin d), ∃ K' : FinExt l, ∀ i ∈ s, ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g (y i) = y i by
    obtain ⟨K', hK'⟩ := h Finset.univ
    exact ⟨K', fun i => hK' i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨K, by simp⟩
  | insert j s hj ih =>
    obtain ⟨K₁, h₁⟩ := ih
    obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (hy j)
    refine ⟨supExt K₁ K₂, fun i hi g hg => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    · exact h₁ i hi g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)

end GlobalTheory.Pst.UnitLetter

set_option maxHeartbeats 1000000 in
open GlobalTheory.Pst.UnitLetter GlobalTheory.NormBC in

theorem GlobalTheory.Pst.UnitLetter.exists_unit_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ {K L : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1), (∀ g v, ρm g v = χ g • v) → IsPst P ρm → ∃ y ∈ Dpst P ρm, ∃ y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' y = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  intro l _ P AI hT K L ρm χ hm hpst
  haveI := L.2
  obtain ⟨hdom, hfrac, hline⟩ := GlobalTheory.Pst.stRegular l P AI hT
  obtain ⟨hfd, hrank⟩ := (isPst_iff P ρm).mp hpst
  set d := finrank ℚ_[l] ↥L.1 with hddef
  have hd : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) = d := by
    rw [hrank]; exact (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1).finrank_eq
  let bD := Module.finBasisOfFinrankEq ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) hd
  let y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρm).symm (bD i) : ↥(Dpst P ρm)).1
  have hyD : ∀ i, y i ∈ Dpst P ρm := fun i => ((toUr P ρm).symm (bD i)).2

  obtain ⟨K', hK'⟩ := exists_common_fixed P ρm y hyD
  let w : Fin d → Bst P ⊗[ℚ_[l]] ↥L.1 := fun i => toA P L (y i)
  let G := {g : ↥(GK K) // (g : GQ l) ∈ GK K'}
  let σ : G → (Bst P ⊗[ℚ_[l]] ↥L.1) →+ (Bst P ⊗[ℚ_[l]] ↥L.1) := fun g => AddMonoidHom.mk' (fun z =>
      Algebra.TensorProduct.map (actSt P ((g.1 : ↥(GK K)) : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) z *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g.1)) (fun a b => by simp [map_add, add_mul])
  have hσ : ∀ (g : G) (b : Bst P) (z : Bst P ⊗[ℚ_[l]] ↥L.1),
      σ g (b • z) = actSt P ((g.1 : ↥(GK K)) : GQ l) b • σ g z := by
    intro g b z
    simp only [σ, AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, mul_assoc]
    congr 1
  have hreg : ∀ b b' : Bst P, b ≠ 0 → (∀ g : G, b * actSt P ((g.1 : ↥(GK K)) : GQ l) b' =
      actSt P ((g.1 : ↥(GK K)) : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b := by
    intro b b' hb h
    obtain ⟨c, -, hc⟩ := hfrac (supExt K K') b b' hb fun g =>
      h ⟨⟨g, GK_le (K' := supExt K K') le_sup_left g.2⟩, GK_le (K' := supExt K K') le_sup_right g.2⟩
    exact ⟨c, hc⟩
  have hv : ∀ (g : G) i, σ g (w i) = w i := by
    intro g i
    simp only [σ, w, AddMonoidHom.mk'_apply]
    rw [← toA_stRep ρm χ hm, hK' i g.1 g.2]
  have hK : LinearIndependent ↥(MaximalUnramifiedExtension l) w := linearIndependent_toA P ρm bD
  have hB : LinearIndependent (Bst P) w := by
    have := GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P)
      (W := Bst P ⊗[ℚ_[l]] ↥L.1)
      (G := G) (fun g => actSt P ((g.1 : ↥(GK K)) : GQ l)) σ hσ hreg w hv Finset.univ
      (hK.linearIndepOn _)
    rw [Finset.coe_univ] at this
    exact linearIndepOn_univ.mp this
  have hfin : finrank (Bst P) (Bst P ⊗[ℚ_[l]] ↥L.1) = d := Module.finrank_baseChange
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero (k := ↥(MaximalUnramifiedExtension l)) w (GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent hfin w hB)
  let ys := ∑ i, mulV P ↥L.1 (Fin 1 → ↥L.1) (a i) (y i)
  have hys : ys ∈ Dpst P ρm := Submodule.sum_mem _ fun i _ => mulV_mem_Dpst P ρm (a i) (y i) (hyD i)
  have hysA : toA P L ys = ∑ i, algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (a i) • w i := by
    simp only [ys, map_sum, toA_mulV, w]
  have hn : Algebra.norm (Bst P) (toA P L ys) ≠ 0 := by rw [hysA]; exact ha
  obtain ⟨K₂, hK₂⟩ := (mem_Dpst P ρm).mp hys
  have hχ : ∀ g : ↥(GK K), χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g * g⁻¹) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by rw [mul_inv_cancel, map_one]; rfl
    rw [map_mul, Module.End.mul_apply, hm g, h0, zero_smul] at h1
    exact zero_ne_one (congrFun h1 0)
  have hunit : IsUnit (Algebra.norm (Bst P) (toA P L ys)) := by
    refine hline (supExt K K₂) _ hn fun g => ?_
    let g0 : ↥(GK K) := ⟨g, GK_le (K' := supExt K K₂) le_sup_left g.2⟩
    have hfix := hK₂ g0 (GK_le (K' := supExt K K₂) le_sup_right g.2)
    have h1 : Algebra.norm (Bst P) (toA P L (stRep P ρm g0 ys)) = Algebra.norm (Bst P) (toA P L ys) := by
      rw [hfix]
    rw [toA_stRep ρm χ hm, map_mul, GlobalTheory.T.norm_tensorProduct_map_id_right, norm_one_tmul] at h1
    have hν : Algebra.norm ℚ_[l] (χ g0) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (hχ g0)
    refine ⟨(Algebra.norm ℚ_[l] (χ g0))⁻¹, ?_⟩
    change actSt P ((g0 : ↥(GK K)) : GQ l) _ = _
    conv_rhs => rw [← h1]
    rw [mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hν, map_one, mul_one]
  obtain ⟨v, hv'⟩ := (isUnit_of_isUnit_norm hunit).exists_right_inv
  refine ⟨ys, hys, (toA P L).symm v, ?_⟩
  apply (toA P L).injective
  rw [toA_mulB, LinearEquiv.apply_symm_apply, toA_tmul, mul_comm, hv']
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodProduct_eq_of_invertible_character : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  first | exact @GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | exact GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | (intros; apply GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  first | exact @GlobalTheory.ParaLevel.exists_parahoric_char | exact GlobalTheory.ParaLevel.exists_parahoric_char | (intros; apply GlobalTheory.ParaLevel.exists_parahoric_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertLocalEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivOutside_inertLocal_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  first | exact @GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq | exact GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq | (intros; apply GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEven
section
open NumberField

namespace GlobalTheory.RealGal

theorem QCM.even_finrank_maximalRealSubfield (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield Q.K) Q.K
  have h2 := Module.finrank_mul_finrank ℚ E Q.K
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield Q.K) Q.K] at h1
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3
  rw [Q.two] at h2
  exact ⟨Module.finrank ℚ (maximalRealSubfield E), by omega⟩

end GlobalTheory.RealGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugationStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_invariant_under_conjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  first | exact @GlobalTheory.PstConj.main | exact GlobalTheory.PstConj.main | (intros; apply GlobalTheory.PstConj.main <;> assumption)
end

