import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainMetric

theorem integ_pair {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [MeasurableSpace X] {μ : Measure X} {A : Set X}
    (f g : (⨂[ℂ] i, E i) →ₗ[ℂ] (X → ℂ)) (B : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) (k : ℂ)
    (h : ∀ v v' : ∀ i, E i, IntegrableOn (fun x => f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
      ∫ x in A, f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ =
        k * B (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v')) :
    ∀ w w', IntegrableOn (fun x => f w x * conj (g w' x)) A μ ∧ ∫ x in A, f w x * conj (g w' x) ∂μ = k * B w w' := by

  have left : ∀ (w : ⨂[ℂ] i, E i) (v' : ∀ i, E i),
      IntegrableOn (fun x => f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
        ∫ x in A, f w x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ = k * B w (PiTensorProduct.tprod ℂ v') := by
    intro w v'
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := h v v'
      have e : (fun x => f (r • PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => r * (f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
        funext x
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.const_mul h1 r
      · rw [e, integral_const_mul, h2]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
    | add a b ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      have e : (fun x => f (a + b) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => f a x * conj (g (PiTensorProduct.tprod ℂ v') x) + f b x * conj (g (PiTensorProduct.tprod ℂ v') x) := by
        funext x
        simp only [map_add, Pi.add_apply, add_mul]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.add ha1 hb1
      · rw [e, integral_add ha1 hb1, ha2, hb2]
        simp only [map_add, LinearMap.add_apply, mul_add]

  intro w w'
  induction w' using PiTensorProduct.induction_on with
  | smul_tprod r v' =>
    obtain ⟨h1, h2⟩ := left w v'
    have e : (fun x => f w x * conj (g (r • PiTensorProduct.tprod ℂ v') x)) =
        fun x => conj r * (f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
      funext x
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.const_mul h1 (conj r)
    · rw [e, integral_const_mul, h2]
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      ring
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have e : (fun x => f w x * conj (g (a + b) x)) =
        fun x => f w x * conj (g a x) + f w x * conj (g b x) := by
      funext x
      simp only [map_add, Pi.add_apply, mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.add ha1 hb1
    · rw [e, integral_add ha1 hb1, ha2, hb2]
      simp only [map_add, mul_add]

variable {D : D7}

theorem val_tprod {V' : HSp D} {S' : D.what₂.Tau → SPar} {M' : DSModel V' S'} (x : (⨂[ℂ] τ, M'.sm τ) →ₗ[ℂ] (GA D V' → ℂ))
    (v : M'.Vec) : x (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm x v := by
  rw [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply]

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.T.exists_inner_product_smooth_vectors_tensor D s.V s.par s.M
  have hθ : IsInfFam c.θ := hc.inf
  have hμ := hs.haar
  have h𝓕 := hs.fund
  have hSM : SchurMult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) s.ν s.fd :=
    GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  have hmem : ∀ x : s.CC c, PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    fun x => (mem_multT c.θ s.M _ _ _).1 x.2
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  ·
    obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M _ _ s.ν s.fd hθ hμ h𝓕 hSM hsm
    have hherm : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ipM s.M s.ν s.fd T' T = star (ipM s.M s.ν s.fd T T') :=
      fun T hT T' hT' => (hlin T hT T' hT' T' hT' 0).2
    have hadd : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ∀ T'' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
            ipM s.M s.ν s.fd T (T' + T'') = ipM s.M s.ν s.fd T T' + ipM s.M s.ν s.fd T T'' := by
      intro T hT T' hT' T'' hT''
      have := (hlin T hT T' hT' T'' hT'' 1).1
      rwa [one_smul, one_mul] at this
    have hzero : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ipM s.M s.ν s.fd T 0 = 0 := by
      intro T hT
      have := hadd T hT 0 (zero_mem _) 0 (zero_mem _)
      rw [add_zero] at this
      linear_combination -this
    have hsmul : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ∀ a : ℂ,
          ipM s.M s.ν s.fd T (a • T') = a * ipM s.M s.ν s.fd T T' := by
      intro T hT T' hT' a
      have := (hlin T hT 0 (zero_mem _) T' hT' a).1
      rwa [zero_add, hzero T hT, zero_add] at this

    have hIP : ∀ x y : s.CC c, ∀ w w',
        IntegrableOn (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g)) s.fd s.ν ∧
        ∫ g in s.fd, (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g * conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g) ∂s.ν =
          ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) * ipD w w' := by
      intro x y
      apply integ_pair
      intro v v'
      have hex := hSM hθ hμ h𝓕 _ (hmem y) _ (hmem x)
      have hc : IsMultIP s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) := by
        rw [ipM, dif_pos hex]
        exact hex.choose_spec
      obtain ⟨h1, h2⟩ := hc v' v
      have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) =
          fun g => star (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' g) *
            PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g := by
        funext g
        rw [val_tprod, val_tprod, mul_comm, starRingEnd_apply]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact h1
      · rw [e, h2, hpure]
    refine ⟨ipD, LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y : s.CC c => ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
        (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) ?_ ?_ ?_ ?_, ?_⟩
    · intro x x' y
      simp only [Submodule.coe_add, map_add]
      exact hadd _ (hmem y) _ (hmem x) _ (hmem x')
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, smul_eq_mul]
      exact hsmul _ (hmem y) _ (hmem x) a
    · intro x y y'
      simp only [Submodule.coe_add, map_add]
      rw [hherm _ (hmem x) _ (add_mem (hmem y) (hmem y')), hadd _ (hmem x) _ (hmem y) _ (hmem y'), star_add,
        ← hherm _ (hmem x) _ (hmem y), ← hherm _ (hmem x) _ (hmem y')]
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul]
      rw [hherm _ (hmem x) _ (Submodule.smul_mem _ a (hmem y)), hsmul _ (hmem x) _ (hmem y), star_mul',
        ← hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
    · refine ⟨hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
      · intro x y
        simp only [LinearMap.mk₂'ₛₗ_apply]
        rw [hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
      · intro x hx
        simp only [LinearMap.mk₂'ₛₗ_apply]
        refine hpos _ (hmem x) fun h0 => hx ?_
        apply Subtype.ext
        rw [Submodule.coe_zero]
        exact (LinearEquiv.map_eq_zero_iff _).1 h0
      · intro x y w w'
        exact (hIP x y w w').1
      · intro x y w w'
        simp only [Lift.pet, LinearMap.mk₂'ₛₗ_apply]
        exact (hIP x y w w').2
  ·
    push_neg at hsm
    obtain ⟨τ₀, hτ₀⟩ := hsm
    have htp : ∀ v : s.M.Vec, PiTensorProduct.tprod ℂ v = 0 := by
      intro v
      apply (PiTensorProduct.tprod ℂ).map_coord_zero τ₀
      have : (v τ₀ : s.M.H τ₀) ∈ (⊥ : Submodule ℂ (s.M.H τ₀)) := hτ₀ ▸ (v τ₀).2
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    have hz : ∀ w : SmT s.M, w = 0 := by
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v => rw [htp v, smul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    refine ⟨ipD, 0, hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp
    · intro x hx
      exfalso
      apply hx
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      rw [hz w]
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp [Lift.pet]

end GlobalTheory.ChainMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelFacts

variable {D : D7}

theorem places_of_stage {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) : s.L.Pg = c.Pg ∧ s.L.Q = ∅ := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  rw [hL]
  exact ⟨rfl, rfl⟩

theorem mem_levG_of_red {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {k : GA D s.V} (hk : k ∈ GfC s.V)
    (hS : Lev.finE s.V k ∈ St s.β) (hr : ∀ PP ∈ c.Pg, redFn s.β PP (Lev.finE s.V k) = 1) :
    k ∈ Lev.levG s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1 := by
  obtain ⟨hPg, hQ⟩ := places_of_stage hs
  have h' : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → redFn s.β PP (Lev.finE s.V k) = 1 := by
    rintro PP (h | h)
    · exact hr PP (hPg ▸ h)
    · rw [hQ] at h; simp at h
  refine ⟨⟨hk, GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm s.V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA s.V k) hS h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one s.β s.L _ h', Units.val_one]

theorem finE_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k : GA D V}
    (hk : k ∈ Lev.levG V β L) : Lev.finE V k ∈ St β :=
  parLev_St (lev_le_parLev hk.2)

theorem emb_mem_GfC (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k ∈ GfC V := by
  rw [GlobalTheory.AdelicU.GfC_eq]
  exact GlobalTheory.AdelicU.mem_finPts.2 (by simp)

theorem levChi_norm {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : GA D V) :
    ‖Lev.levChi V β L k‖ = 1 := by
  obtain ⟨n, hn, h⟩ := (GlobalTheory.LevSplit.levFn_finOrd β L (Lev.finE V k)).exists_pow_eq_one
  have h2 : (Lev.levChi V β L k) ^ n = 1 := by
    unfold Lev.levChi
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'

theorem levChi_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  have e := (levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : levFn β L (Lev.finE V k * Lev.finE V k') = levFn β L (Lev.finE V k) * levFn β L (Lev.finE V k') := e
  unfold Lev.levChi
  rw [map_mul, e', Units.val_mul]

end GlobalTheory.ChainOnto.LevelFacts

namespace GlobalTheory.ChainOnto.LevelFacts

theorem levFacts : ∀ D : D7, LevFacts D := by
  intro D c _ j _ s hs
  have hfr := hs.frame
  have hPS : ∀ PP ∈ c.Pg, PP.under (𝓞 D.host.F) ∈ c.S := fun PP hPP => by
    classical
    unfold Com.S
    exact Finset.mem_image_of_mem _ hPP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D s.V s.β c.Pg
    exact ⟨U, hU, fun k hk hkf => mem_levG_of_red hs hkf (hUk k hk).1 (hUk k hk).2⟩
  · intro v hv k hk
    have hSt : Lev.finE s.V (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) ∈ St s.β := by
      refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr _).2 fun w => ?_
      by_cases e : w = v
      · subst e
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact hk
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
        exact one_mem _
    refine mem_levG_of_red hs (emb_mem_GfC s.V v k) hSt fun PP hPP => ?_
    · refine GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β _ PP hSt ?_
      have hne : PP.under (𝓞 D.host.F) ≠ v := fun e => hv (e ▸ hPS PP hPP)
      exact GlobalTheory.AdelicU.proj_emb_ne _ _ hne k
  · intro k hk v
    exact (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).1 (finE_mem_St hk) v
  · intro k hkf hint h1
    have hSt : Lev.finE s.V k ∈ St s.β := by
      refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).2 fun v => ?_
      by_cases hv : v ∈ c.S
      · rw [h1 v hv]; exact one_mem _
      · exact hint v hv
    exact mem_levG_of_red hs hkf hSt fun PP hPP => GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β k PP hSt (h1 _ (hPS PP hPP))
  · intro k hk k' hk'
    exact levChi_mul hk hk'
  · intro k _
    exact levChi_norm s.β s.L k

end GlobalTheory.ChainOnto.LevelFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_chainUp : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨hs, hadj⟩ := hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := GlobalTheory.T.thetaChainHeckeParam_add_smul_of_agree_off_set D c s₀
  refine GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise D c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

variable {D : D7}

theorem rapidDec_val (hP : GlobalTheory.Published.CuspRapidDecay) {c : Com D} (hc : c.Is) {s : PiLocalization₂ D} (u : s.CC c)
    (v : SmT s.M) : GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v) := by
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w =>
    have h1 := GlobalTheory.Grow.rapidDec_of_cuspForm hP hc.inf (hM.aut w) (hM.cusp w)
    have h2 : PiLocalization₂.val u (r • PiTensorProduct.tprod ℂ w) =
        r • PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w := by
      simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    rw [h2]
    exact Grow.RapidDec.smul r h1
  | add x y hx hy =>
    have : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := by simp [PiLocalization₂.val]
    rw [this]; exact hx.add hy

theorem upAdj_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  intro hP D _ c hc k _ s s' hs hs' p hp u y φ v _ w _
  have hF := GlobalTheory.T.thetaKernel_iterated_integrals_swap D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hc.inf hp.weil (p.pt φ) (hp.theta φ)
    s.ν s.fd s'.ν s'.fd hs.haar hs.fund hs'.haar hs'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w)
    (rapidDec_val hP hc u v) (rapidDec_val hP hc y w)
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w) g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w g

end GlobalTheory.ChainOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChainTw.StepExpTw

theorem twStepExpVac : ∀ D : D7, ForStepQ D fun c _ k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (GlobalTheory.Chain.expS D ⟨k, hk⟩) (GlobalTheory.Chain.expT D ⟨k, hk⟩) p.ω ∧
      GlobalTheory.Chain.IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c w hw k _ s s' hs hs' p hp hk
  obtain ⟨hr, _, hsf⟩ := hs
  obtain ⟨hr', _, hsf'⟩ := hs'
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => StepExp.chrStep_exp' hw.com ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨f₀, hv⟩ := hp.vec
  have hrk : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hsf.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hsf'.rank
    rw [h1, h2]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.R.t (Nat.le_succ k)) D.R.r
  obtain ⟨a, b, d⟩ := StepVac.stepVec_vac hsf.selfDual hsf'.selfDual hrk hv
  exact { theta := a, ne := b, vac := d }

end GlobalTheory.ChainTw.StepExpTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_char_trivial_on_integral_units_at_place : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle, (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  first | exact @GlobalTheory.UnrPlDict.unrPl_of_unrAt | exact GlobalTheory.UnrPlDict.unrPl_of_unrAt | (intros; apply GlobalTheory.UnrPlDict.unrPl_of_unrAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_doubling_integral_inert_adelic : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.LocZetaInertAd.localZetaOn_inert | exact GlobalTheory.LocZetaInertAd.localZetaOn_inert | (intros; apply GlobalTheory.LocZetaInertAd.localZetaOn_inert <;> assumption)
end

