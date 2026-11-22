import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrank
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_conjRows_eq {D : D7} (X : HidaSetting D) :
    Module.finrank ℂ (conjRows X) = Module.finrank ℂ (HHX X) := by
  let e := conjL (muX X)
  let j : conjRows X ≃+ HHX X :=
    { toFun := fun f => ⟨e f, f.2⟩
      invFun := fun g => ⟨e.symm g, by
        show e.toLinearEquiv.toLinearMap (e.symm g) ∈ HHX X
        simpa using g.2⟩
      left_inv := fun f => by ext1; simp
      right_inv := fun g => by ext1; simp
      map_add' := fun f g => by ext1; simp }
  have hbij : Function.Bijective (starRingEnd ℂ : ℂ → ℂ) :=
    Function.Involutive.bijective (fun z => by simp)
  have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ : ℂ → ℂ) j hbij (fun r m => by
    ext1
    show e (r • (m : L2X X)) = (starRingEnd ℂ r) • e m
    exact e.map_smulₛₗ r m)
  unfold Module.finrank
  rw [hr]

theorem exists_rowJ_and_finrank_HHX : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c eE hc hv₀ hE hrange hnorm hle hJ1 hJ2
  refine ⟨fun hD => ?_, exists_rowJ_of_evalOn hc hv₀ hE hrange hnorm hle hJ2⟩
  obtain ⟨J1, -⟩ := hJ1
  have hD' : D.what₂.Dall = Module.finrank ℂ (MultR R F) := hD
  rw [hD', J1.finrank_eq, finrank_conjRows_eq]

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportGroupsCuspFormsWeilDataIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.Isom

variable {D : D7}

theorem gelf_tr {V V' : HSp D} (I : IsoMat V V') {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ}
    (hφ : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) : gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) :=
  GlobalTheory.T.gelfand_operator_commutes_isometry D V V' I θ hθ τ k φ hφ

theorem cusp_tr {V V' : HSp D} (I : IsoMat V V') {φ : GA D V → ℂ} (hφ : IsCuspFun V φ) : IsCuspFun V' (I.tr φ) :=
  GlobalTheory.T.isCuspidal_isometryTransport_hermitian D V V' I φ hφ

theorem haar_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL V' S) 𝓕 μ) : ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧
        ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν :=
  GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport D V V' I S μ 𝓕 hμ h𝓕

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

theorem isAutFun_tr {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V' (I.tr φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp I.continuous_kap_symm⟩
  · unfold tr
    rw [map_mul]
    exact h.left _ (I.symm.kap_mem_GQ hγ) _
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap I.kap.symm.toMonoidHom, hU.preimage I.continuous_kap_symm, fun k hk hf g => ?_⟩
    unfold tr
    rw [map_mul]
    exact e _ hk (I.symm.kap_mem_GfC hf) _

theorem normInf_kap_le (hθ : IsInfFam θ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g :=
  GlobalTheory.T.normInf_isometryConj_le_const_mul D V V' I θ hθ

theorem foldr_tr (hθ : IsInfFam θ) (φ : GA D V → ℂ) (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    l.foldr (fun p f => Rder θ V' p.1 p.2 f) (I.tr φ) =
      I.tr ((l.map fun p => (p.1, I.symm.adP p.1 p.2)).foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      I.Rder_tr hθ (hl p List.mem_cons_self)]

def trLin : (GA D V → ℂ) →ₗ[ℂ] (GA D V' → ℂ) where
  toFun := I.tr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFunSm_tr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V' (I.tr φ) := by
  have ha := I.isAutFun_tr hφ.toIsAutFun
  refine { left := ha.left, level := ha.level, cont := ha.cont, smooth := I.tr_mem_SmFun hθ hφ.smooth, zfin := ?_, growth := ?_ }
  · obtain ⟨W, hW, m, s⟩ := hφ.zfin
    refine ⟨(W ⊓ GlobalTheory.Mem.AutSpace.SmFun θ V).map I.trLin, inferInstance, ⟨φ, ⟨m, hφ.smooth⟩, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, ⟨s τ k f hf.1, (GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).mem f hf.2⟩, (_root_.GlobalTheory.Mem.Isom.gelf_tr I hθ τ k hf.2).symm⟩
  · obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨c, hc0, hc⟩ := I.symm.normInf_kap_le hθ
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN (l.map fun p => (p.1, I.symm.adP p.1 p.2)) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact I.symm.adP_mem (hl q hq)) (I.kap.symm x)
    refine ⟨|C| * c ^ N, fun g hg => ?_⟩
    rw [I.foldr_tr hθ φ l hl]
    unfold tr
    rw [map_mul, mul_assoc |C|, ← mul_pow]
    exact (hC _ (I.symm.kap_mem_GinfC hg)).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) (hc g) N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
      (abs_nonneg _))

theorem isThetaFunO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ} (hf : IsThetaFunO ψ S V f) :
    IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add, I.symplOH_phi]
    simp only [trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [trW] using this

end IsoMat

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V')

theorem isWeilDatumO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : IdC D} {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => I.symm.isThetaFunO_tr S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact I.isThetaFunO_tr S (h.om_pres _ _ (hT f hf))
  · rw [omT_apply, omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := haar_tr I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (I.isThetaFunO_tr S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

end IsoMat

theorem exists_isom_transport : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), HSpace.IsIsomEmb V V' e.toLinearMap →
    ∃ κ : GA D V ≃* GA D V', Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧
      (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om →
        ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f → ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧
          ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f := by
  intro D V V' e he
  let I := IsoMat.ofEquiv e he
  refine ⟨I.kap, I.continuous_kap, I.continuous_kap_symm, fun g => ⟨fun hg => ?_, I.kap_mem_GQ⟩,
    fun θ hθ F hF => ⟨I.isAutFunSm_tr hθ hF.1, cusp_tr I hF.2⟩, fun ψ S χ χ' om hom => ?_⟩
  · have := I.symm.kap_mem_GQ hg
    rwa [← I.kap_symm_apply, I.kap.symm_apply_apply] at this
  · refine ⟨I.omT S om, I.isWeilDatumO_tr S hom, fun f hf => ⟨I.trW S f, I.isThetaFunO_tr S hf, fun hne h0 => hne ?_, fun g h => ?_⟩⟩
    · have := I.trW_symm_trW S f
      rw [h0] at this
      rw [← this]
      rfl
    · show I.trW S (om (g, I.kap.symm (I.kap h)) (I.symm.trW S (I.trW S f))) 0 = om (g, h) f 0
      rw [I.kap.symm_apply_apply, I.trW_symm_trW]
      show om (g, h) f ((I.phi S).symm 0) = om (g, h) f 0
      rw [map_zero]

end GlobalTheory.Mem.Isom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteExceptionalPlacesOverPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlacesExc

theorem finite_exceptional : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  intro D l hl
  have h1 : (placesOver D.host.E l).Finite := Formalism.L2.Fam.NPC.placesOver_fin D.host l hl
  have h2 : (placesS D l).Finite := Formalism.L2.Fam.NPC.exceptional_places_finite D.host l
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset] at hv
  exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩

end GlobalTheory.PlacesExc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem prod_list_apply_multilinear {ι G V : Type} [DecidableEq ι] [Group G] [AddCommGroup V] [Module ℂ V]
    {H : ι → Type} [∀ v, Group (H v)] {Wv : ι → Type} [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
    (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v))
    (F : MultilinearMap ℂ Wv V)
    (hF : ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))))
    (y : ∀ v, H v) (u : ∀ v, Wv v) :
    ∀ L : List ι, L.Nodup →
      ρ (L.map fun v => s v (y v)).prod (F u) = F fun v => if v ∈ L then σ v (y v) (u v) else u v := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih hL.2, hF]
    congr 1
    funext v
    by_cases hv : v = a
    · rw [hv, Function.update_self]
      simp [hL.1]
    · rw [Function.update_of_ne hv]
      simp [hv]

theorem AutSub.finPart_wt_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    π.finPart (AU.mk π).wt ≠ ⊥ := by
  intro E _ _ _ n π
  classical
  have hW' : ∀ v : InfinitePlace E, HasWeightAt π.V v.embedding ((AU.mk π).wt v) := fun v => by
    obtain ⟨lam, hlam, -⟩ := GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk π) v.embedding
    have h := hlam.wt
    rw [Wt.at_embedding] at h
    exact (AU.hasWt_mk π _ _).1 h
  generalize (AU.mk π).wt = W at hW' ⊢
  have hW := hW'
  clear hW'
  let s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n := fun v => (embU n v.embedding).subtype
  let σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (W v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (W v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    obtain ⟨h1, h2⟩ := (CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (W v))
    refine (CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have := hS x w hw
    change GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (x : UA E n)) w ∈ S at this
    change GlobalTheory.Branching.sqRep ℂ n (W v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding])
      _ a.2 _ b.2
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π v.embedding (W v) (hW v)
  haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π.V (fun v => embU n v.embedding)
    (fun v => nablaSq ℂ n (W v)) π.rep s σ inferInstance hirr hcomm hspan
  obtain ⟨f0, hf0, -⟩ := GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W π.V F
  let f : W.Sp →ₗ[ℂ] (UA E n → ℂ) := π.V.subtype ∘ₗ f0
  have hten : ∀ (g : InfinitePlace E → GL (Fin n) ℂ) (u : ∀ v, nablaSq ℂ n (W v)),
      Formalism.L2.DIV.rhoK W g (GlobalTheory.CoefIrred.tenMul (K := ℂ) W u) =
        GlobalTheory.CoefIrred.tenMul (K := ℂ) W fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v) (u v) := fun g u => by
    apply Subtype.ext
    rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen, GlobalTheory.CoefIrred.tenMul_coe]
    rfl
  have hint : ∀ (x : infU E n) (w : W.Sp), f (W.rep x w) = RU E n x (f w) := by
    intro x w
    obtain ⟨y, hy, hyc, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x.1 x.2
    let y' : ∀ v : InfinitePlace E, embU n v.embedding := fun v => ⟨y v, hy v⟩
    have key : ∀ u, f (W.rep x (GlobalTheory.CoefIrred.tenMul W u)) = RU E n x (f (GlobalTheory.CoefIrred.tenMul W u)) := by
      intro u
      have h1 := prod_list_apply_multilinear π.rep s σ F hF y' u Finset.univ.toList (Finset.nodup_toList _)
      have h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x.1 := hprod
      rw [h2] at h1
      have h3 : W.rep x (GlobalTheory.CoefIrred.tenMul W u) = GlobalTheory.CoefIrred.tenMul W fun v => σ v (y' v) (u v) := by
        change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
        rw [hten]
        refine congrArg (GlobalTheory.CoefIrred.tenMul W) (funext fun v => ?_)
        change _ = GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (y v)) (u v)
        rw [hyc v]
        rfl
      show (f0 (W.rep x (GlobalTheory.CoefIrred.tenMul W u))).1 = RU E n x (f0 (GlobalTheory.CoefIrred.tenMul W u)).1
      rw [h3, hf0, hf0, ← AutSub.rep_val, h1]
      simp only [Finset.mem_toList, Finset.mem_univ, if_true]
    have := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W (UA E n → ℂ)
      ((f ∘ₗ W.rep x).compMultilinearMap (GlobalTheory.CoefIrred.tenMul W))).unique
      (y₁ := f ∘ₗ W.rep x) (y₂ := RU E n x ∘ₗ f) (fun u => (LinearMap.compMultilinearMap_apply _ _ _).symm)
      (fun u => by rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply]; exact (key u).symm)
    exact LinearMap.congr_fun this w
  have hmem : f ∈ algForms W := ⟨fun w => π.le_autU (f0 w).2, hint⟩
  have hfin : (⟨f, hmem⟩ : algForms W) ∈ π.finPart W := AutSub.mem_finPart.2 fun w => (f0 w).2
  obtain ⟨u, hu⟩ : ∃ u, F u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF0 (MultilinearMap.ext h)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨f, hmem⟩, hfin, fun h => hu ?_⟩
  have := LinearMap.congr_fun (congrArg Subtype.val h) (GlobalTheory.CoefIrred.tenMul W u)
  rw [← hf0]
  exact Subtype.ext this

end GlobalTheory.DefU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePlacesLgNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem finite_places_lg_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ y : AlgPt Y, {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, A.lg v e y ≠ 0}.Finite := by
  intro F _ _ C Y A M L k cf hI y
  obtain ⟨hcf, r, -, -, hfin⟩ := hI
  have := M.ar.isNoetherian
  have hcov : (Set.univ : Set M.X) ⊆ ⋃ i, (L.B.U i : Set M.X) := by
    intro x _
    have hx : x ∈ (⨆ i, L.B.U i : M.X.Opens) := by rw [L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.B.U i : Set M.X))
    (fun i => (L.B.U i).isOpen) hcov
  let a : L.B.ι → AlgebraicClosure F := fun i =>
    valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r (fun _ => i) : Y.Fnˣ) : Y.Fn)
  have hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | a i ≠ 0 ∧ ∃ e : Ext v, e.w (a i) ≠ 1}.Finite := by
    intro i
    by_cases h : a i = 0
    · simp [h]
    · exact (GlobalTheory.TrueGeo.finite_ext_ne_one F (a i) h).subset fun v hv => hv.2
  refine (hcf.union (S.finite_toSet.biUnion fun i _ => hB i)).subset ?_
  rintro v ⟨e, he⟩
  obtain ⟨yt, hyt, hU⟩ := GlobalTheory.TrueGeo.exists_valuationRing_point F Y M v e y
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h := hfin v e y yt (fun _ => i) hyt (hU _ hi).1
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h1' : cf v = 0 := by simpa using h1
  have hlog : Real.log (e.w (a i)) = 0 := by
    by_cases h0 : a i = 0
    · simp [h0]
    · have : e.w (a i) = 1 := by
        by_contra hne
        exact h2 (Set.mem_iUnion₂.mpr ⟨i, hiS, h0, e, hne⟩)
      simp [this]
  have h3 : ((k : ℕ) : ℝ) * A.lg v e y = 0 := by
    rw [h, h1', mul_zero, sub_zero]
    exact hlog
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  exact he ((mul_eq_zero.mp h3).resolve_left hk)

end GlobalTheory.TrueGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGenericStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlag_common_closedPoint_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  first | exact @GlobalTheory.FlagBundle.coBear_closedPoint | exact GlobalTheory.FlagBundle.coBear_closedPoint | (intros; apply GlobalTheory.FlagBundle.coBear_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyCrystallineWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MuCLoc

theorem exists_muC : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  refine ⟨A.chr.e1.symm ⟨tp.tup (X.nd.mu i) j, tp.tup_unitary (X.nd.mu i) j⟩, ?_, ?_⟩
  · rw [A.chr.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ ((cf.isMu0 j).triv.mul (tp.xi_triv (X.nd.mu i)))
  · intro j' hj'
    have : j' = j := Fin.ext (by simp only [j]; omega)
    subst this
    rw [Equiv.apply_symm_apply]

end GlobalTheory.MuCLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocalStatement
section
open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_finite_idelic_iff_local : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) = χ.1 (finId H.E u)) ↔ ∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdFin_iff | exact GlobalTheory.CuspRep.csdFin_iff | (intros; apply GlobalTheory.CuspRep.csdFin_iff <;> assumption)
end

