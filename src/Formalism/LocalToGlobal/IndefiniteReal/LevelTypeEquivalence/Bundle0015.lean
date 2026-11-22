import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ShiftedBound
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.IoExist
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasFr

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FatouOm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem fatou_om {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {L : (Fin k → ℝ) →+ WO S T} {P : WO S T →+ (Fin k → ℝ)}
    (hL : IsRealFrame L) (hPc : Continuous P) (hLP : ∀ w, L (P w) = eInf D • w) (g : GA D S) (h : GA D T)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} (l : Fin n → Fin k) :
    ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ ≤
      ∫⁻ x in 𝓕, ‖dH ψ ((actOAdd g⁻¹ h⁻¹).comp L) l f x‖ₑ ^ 2 ∂μ := by
  have hψ := hω.std
  obtain ⟨Λ, hΛ, hψΛ⟩ := psi_real ψ hψ
  obtain ⟨hM, hPMc, hMP⟩ := transported_frame hL hPc hLP g h
  set M := (actOAdd g⁻¹ h⁻¹).comp L
  set v : Fin n → (Fin k → ℝ) := fun i => ev (l i)
  set hj : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hjpos : ∀ j, 0 < hj j := fun j => by positivity
  have hjle : ∀ j, hj j ≤ 1 := fun j => by
    simp only [hj]; rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  set Tf : ℕ → WO S T → ℂ := fun j y => md (Gf ψ M f y) n v (hj j) 0
  have hT : ∀ j, IsThetaFunO ψ S T (Tf j) := fun j => md_theta hψ hf hM n v (hj j) 0
  have hom : ∀ j, om (g, h) (Tf j) = fun x => md (Gf ψ L (om (g, h) f) x) n v (hj j) 0 := fun j =>
    om_md hω hf L hL g h n v (hj j) 0
  have hf' : IsThetaFunO ψ S T (om (g, h) f) := hω.om_pres (g, h) f hf
  have hlimL : ∀ x, Tendsto (fun j => om (g, h) (Tf j) x) atTop (𝓝 (dH ψ L l (om (g, h) f) x)) := by
    intro x
    have e : (fun j => om (g, h) (Tf j) x) = fun j => md (Gf ψ L (om (g, h) f) x) n v (hj j) 0 :=
      funext fun j => congrFun (hom j) x
    rw [e]
    exact md_tendsto_seq (Gf_smooth hΛ hψΛ hL hf' x) v
  have hlimM : ∀ y, Tendsto (fun j => Tf j y) atTop (𝓝 (dH ψ M l f y)) := fun y =>
    md_tendsto_seq (Gf_smooth hΛ hψΛ hM hf y) v
  obtain ⟨B, hB⟩ := shifted_bound hψ hf hM hPMc hMP n (n : ℝ) (Nat.cast_nonneg n)
  have hTb : ∀ j y, ‖Tf j y‖ ≤ B := by
    intro j y
    have := md_bound n (Gf ψ M f y) (Gf_smooth hΛ hψΛ hM hf y) v (hj j) (hjpos j) 0 B (fun t ht => hB y t (by
      have hsum : ∑ i, ‖v i‖ = n := by simp [v, norm_ev]
      rw [sub_zero, hsum] at ht
      calc ‖t‖ ≤ hj j * n := ht
        _ ≤ 1 * n := mul_le_mul_of_nonneg_right (hjle j) (Nat.cast_nonneg n)
        _ = n := one_mul _))
    simpa [v, norm_ev] using this

  have hF : ∀ x, Tendsto (fun j => ‖om (g, h) (Tf j) x‖ₑ ^ 2) atTop (𝓝 (‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2)) :=
    fun x => ((ENNReal.continuous_pow 2).comp continuous_enorm).continuousAt.tendsto.comp (hlimL x)
  have hmeas : ∀ j, Measurable fun x => ‖om (g, h) (Tf j) x‖ₑ ^ 2 := fun j =>
    (hω.om_pres (g, h) _ (hT j)).cont.enorm.measurable.pow_const 2
  have step1 : ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ ≤
      liminf (fun j => ∫⁻ x in 𝓕, ‖om (g, h) (Tf j) x‖ₑ ^ 2 ∂μ) atTop := by
    calc ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ
        = ∫⁻ x in 𝓕, liminf (fun j => ‖om (g, h) (Tf j) x‖ₑ ^ 2) atTop ∂μ :=
          lintegral_congr fun x => ((hF x).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le (u := atTop) (f := fun j x => ‖om (g, h) (Tf j) x‖ₑ ^ 2) hmeas
  have step2 : ∀ j, ∫⁻ x in 𝓕, ‖om (g, h) (Tf j) x‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖Tf j x‖ₑ ^ 2 ∂μ := fun j =>
    hω.om_unit μ 𝓕 hμ h𝓕 (g, h) (Tf j) (hT j)
  have hfin : μ 𝓕 < ⊤ := (PHeisFC.finCovol T S).2 μ 𝓕 hμ h𝓕
  have step3 : Tendsto (fun j => ∫⁻ x in 𝓕, ‖Tf j x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x in 𝓕, ‖dH ψ M l f x‖ₑ ^ 2 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ‖(B : ℂ)‖ₑ ^ 2)
      (fun j => (hT j).cont.enorm.measurable.pow_const 2) (fun j => Eventually.of_forall fun y => ?_) ?_
      (Eventually.of_forall fun y => ((ENNReal.continuous_pow 2).comp continuous_enorm).continuousAt.tendsto.comp
        (hlimM y))
    · show ‖Tf j y‖ₑ ^ 2 ≤ ‖(B : ℂ)‖ₑ ^ 2
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hTb j y).trans (by rw [Complex.norm_real]; exact le_abs_self B))
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) hfin.ne
  calc ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ
      ≤ liminf (fun j => ∫⁻ x in 𝓕, ‖om (g, h) (Tf j) x‖ₑ ^ 2 ∂μ) atTop := step1
    _ = liminf (fun j => ∫⁻ x in 𝓕, ‖Tf j x‖ₑ ^ 2 ∂μ) atTop := by simp_rw [step2]
    _ = _ := step3.liminf_eq

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSelfDualC_of_base {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ N) : IsSelfDualC V Λ := by
  obtain ⟨-, hdual, hN, hin, hout⟩ := hB
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hl0 := (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.self_dual_lattice_is_self_dual V).1
  let φ : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
  have hφ : ∀ x, φ x = (N : D.host.E) • x := fun x => by
    simp only [φ, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) x, map_natCast]
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · have hφinj : Function.Injective φ := fun a b hab => by
      rw [hφ, hφ] at hab
      exact smul_right_injective _ hN0 hab
    have hle : Λ.map φ ≤ Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set, hφ]
      exact hout x hx
    have : IsNoetherian (𝓞 D.host.E) (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V) := isNoetherian_of_fg_of_noetherian _ hl0.fg
    have h1 : ((Λ.map φ).comap (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Submodule.fg_of_fg_map_injective φ hφinj h2
  · rw [eq_top_iff, ← hl0.span_eq_top, Submodule.span_le]
    intro x hx
    have hNx : (N : D.host.E) • x ∈ Λ := hin x ((Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set V x).1 hx)
    have : x = (N : D.host.E)⁻¹ • ((N : D.host.E) • x) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
    have key : (N : D.host.E)⁻¹ • ((N : D.host.E) • x) ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.smul_mem _ _ (Submodule.subset_span hNx)
    rw [← this] at key
    exact key
  · rw [Formalism.IndefR.Eqv.dual_of_dualL hdual y]
    simp only [Formalism.UG.hform, starRingEnd_apply, RingHom.mem_range]

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) :
    ∃ (p : ℕ) (σ : Fin n ≃ Fin n), ∀ a : Fin n, (ε (σ a) = true ↔ a.val < p) := by
  classical
  let P := {i : Fin n // ε i = true}
  let Q := {i : Fin n // ¬ ε i = true}
  have hcard : Fintype.card P + Fintype.card Q = n := by
    have h1 : Fintype.card Q = n - Fintype.card P := by
      show Fintype.card {i : Fin n // ¬ ε i = true} = n - Fintype.card {i : Fin n // ε i = true}
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have h2 : Fintype.card P ≤ n := by
      show Fintype.card {i : Fin n // ε i = true} ≤ n
      have := Fintype.card_subtype_le (fun i : Fin n => ε i = true)
      rwa [Fintype.card_fin] at this
    rw [h1]
    omega
  let e : Fin n ≃ P ⊕ Q := (Equiv.sumCompl (fun i : Fin n => ε i = true)).symm
  let f : P ⊕ Q ≃ Fin (Fintype.card P) ⊕ Fin (Fintype.card Q) := (Fintype.equivFin P).sumCongr (Fintype.equivFin Q)
  let g : Fin (Fintype.card P) ⊕ Fin (Fintype.card Q) ≃ Fin n := finSumFinEquiv.trans (finCongr hcard)
  refine ⟨Fintype.card P, (e.trans (f.trans g)).symm, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := g.surjective a
  have hx : (e.trans (f.trans g)).symm (g x) = e.symm (f.symm x) := by
    simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rw [hx]
  rcases x with x | x
  · have h1 : e.symm (f.symm (Sum.inl x)) = ((Fintype.equivFin P).symm x).1 := by
      simp [e, f, Equiv.sumCompl]
    have h2 : (g (Sum.inl x)).val = x.val := by simp [g]
    rw [h1, h2]
    simp only [((Fintype.equivFin P).symm x).2, true_iff]
    exact x.2
  · have h1 : e.symm (f.symm (Sum.inr x)) = ((Fintype.equivFin Q).symm x).1 := by
      simp [e, f, Equiv.sumCompl]
    have h2 : (g (Sum.inr x)).val = Fintype.card P + x.val := by simp [g]
    rw [h1, h2]
    have := ((Fintype.equivFin Q).symm x).2
    simp only [Bool.not_eq_true] at this
    simp [this]

theorem exists_onb {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ), IsONBasis (gramAt D V τ) (Formalism.IndefR.Links.cart M τ) B p := by
  obtain ⟨p, σ, hσ⟩ := exists_sort (M.ε τ)
  have hu : IsUnit (M.fr τ) := M.fr_unit τ
  have hinv : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hinv' : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  let B := ((M.fr τ)⁻¹).submatrix id σ
  let ε' : Fin V.rank → ℝ := fun a => if M.ε τ (σ a) then 1 else -1
  have hG : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]
    calc ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹
        = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv']; simp
  have hC : Formalism.IndefR.Links.cart M τ * (M.fr τ)⁻¹ = (M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.IndefR.Links.cart
    simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
  have hJ : (Formalism.REAL.Jm (M.ε τ)).submatrix σ σ = Matrix.diagonal fun a => ((ε' a : ℝ) : ℂ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1; funext a
    simp only [ε']
    by_cases h : M.ε τ (σ a) = true <;> simp [h]
  refine ⟨B, p, ε', fun a => ?_, ?_, ?_⟩
  · by_cases h : M.ε τ (σ a) = true
    · left; exact ⟨by simp [ε', h], (hσ a).1 h⟩
    · right
      have hf : M.ε τ (σ a) = false := by simpa using h
      refine ⟨by simp [ε', hf], ?_⟩
      by_contra hlt
      exact h ((hσ a).2 (not_le.1 hlt))
  · show (((M.fr τ)⁻¹).submatrix id σ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹).submatrix id σ = _
    rw [← hJ, ← hG]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.conjTranspose_apply]
  · show Formalism.IndefR.Links.cart M τ * ((M.fr τ)⁻¹).submatrix id σ = ((M.fr τ)⁻¹).submatrix id σ * _
    rw [← hJ]
    ext i j
    have h1 := congrFun (congrFun hC i) (σ j)
    simp only [Matrix.mul_apply] at h1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    rw [h1]
    exact (Equiv.sum_comp σ (fun k => (M.fr τ)⁻¹ i k * Formalism.REAL.Jm (M.ε τ) k (σ j))).symm

section R

open Formalism.IndefR.Links Formalism.IndefR.Links.RealDat

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

open Classical in

theorem sideYR_of (hLev : R.toLevCh.Is A.μ0) (hC : R.IsChain) {t : T} {k : ℕ} (hk : k + 1 < D.R.m)
    (hdisj : Disjoint R.Pg (R.Q t))
    (hsph : Formalism.IndefR.WeilFull.SphInertAtO R.ψ (Yc D k) (Yc D (k + 1))
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k))
    (hunr : ∀ e, IsIdemSum e ((R.datYt t k R.triv).Pg ∪ R.Q t) →
      Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
        Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2)
    (htG : ∀ PP ∈ (R.datYt t k R.triv).Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.chi (k + 1) PP) (-1) ∧
        Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.chi (k + 1) PP) (-1))
    (htQ : ∀ PP ∈ R.Q t, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.xiR t PP) 1 ∧
        Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.xiR t PP) 1) :
    SideYR R t k := by
  obtain ⟨cS, hBS⟩ := hLev.βY k (by omega)
  obtain ⟨cT, hBT⟩ := hLev.βY (k + 1) hk
  choose BS pS hS using fun τ => exists_onb (R.MY k) τ
  choose BT pT hT using fun τ => exists_onb (R.MY (k + 1)) τ
  refine ⟨⟨BS, BT, pS, pT, ?_⟩, hsph, hunr, htG, htQ⟩
  exact
    { cartS := fun τ => Formalism.IndefR.Fock.IoExist.cart_isCartanInv (R.MY k) τ
      cartT := fun τ => Formalism.IndefR.Fock.IoExist.cart_isCartanInv (R.MY (k + 1)) τ
      onbS := hS
      onbT := hT
      frS := hBS.1
      frT := hBT.1
      sdS := isSelfDualC_of_base hBS
      sdT := isSelfDualC_of_base hBT
      disj := hdisj
      vec := hC.vY t k hk }

end R

end Formalism.IndefR.Eqv.KerDiag

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem finHom_eq_one_iff (h : GA D V) : finHom V h = 1 ↔ Lev.finE V h = 1 := by
  unfold Lev.finE
  rw [MonoidHom.comp_apply]
  refine ⟨fun h1 => by rw [h1, map_one], fun h1 => ?_⟩
  have hinj : Function.Injective (Formalism.IndefR.Lev.swapAE D) := by
    intro a b hab
    unfold Formalism.IndefR.Lev.swapAE at hab
    simpa using hab
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g => (Units.val g) i j) h1
  simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Units.val_one] at h2
  apply hinj
  refine Eq.trans h2 ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem brg_mem_GinfC (fr : UI.Frames D V) (x : (UI.instV fr).GA) : UI.brg fr x ∈ GinfC V ↔ x.2 = 1 := by
  unfold GinfC
  rw [MonoidHom.mem_ker, finHom_eq_one_iff, ← Units.val_eq_one]
  have hb := (UI.brg_isBridge fr x).2
  have hz : ∀ z, Formalism.IndefR.Lev.swapAE D (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)
      (AlgHom.id D.host.F D.host.E) z) = (Algebra.TensorProduct.lift ((Algebra.TensorProduct.includeRight : Formalism.MainNotions.S.Af D.host.F →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F).comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)) (Algebra.TensorProduct.includeLeft : D.host.E →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) (fun _ _ => Commute.all _ _)) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).symm
    | tmul a e => simp [Formalism.IndefR.Lev.swapAE, Algebra.TensorProduct.tmul_mul_tmul]
    | add y w hy hw => erw [map_add, map_add, hy, hw, map_add]
  have key : Units.val (Lev.finE V (UI.brg fr x)) =
      Formalism.L2.SG.AdBridge.ofHAFin (UI.instV fr) (UI.brg fr x) := by
    ext i j
    exact hz _
  rw [key]
  constructor
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := hb.trans h1
    simpa [Units.val_eq_one] using h2
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := by simp [h1]
    exact hb.symm.trans h2

theorem ginf_compact (F : MF.FrA V) (hD : V.IsDefinite) : CompactSpace (UI.instV (MF.toFrames F)).Ginf := by
  have hc : ∀ v : InfinitePlace D.host.F, CompactSpace (Formalism.REAL.UJ ((MF.toFrames F).ε v)) := by
    intro v
    haveI : CompactSpace (UpqT (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).1
        (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).2) := by
      rcases hD (tauE D ((Formalism.L2.Host.tauPl D).symm v)) with h | h
      · rw [h]; infer_instance
      · rw [h]; infer_instance
    exact (MF.phiR F v).toHomeomorph.compactSpace
  exact @Pi.compactSpace _ _ (fun _ => inferInstance) hc

theorem isCompact_GinfC (hS : V.SigOK) (hD : V.IsDefinite) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  haveI := ginf_compact F hD
  have e : (GinfC V : Set (GA D V)) = UI.brg (MF.toFrames F) '' (Set.univ ×ˢ {1}) := by
    ext h
    obtain ⟨x, rfl⟩ := (UI.brg (MF.toFrames F)).surjective h
    rw [SetLike.mem_coe, brg_mem_GinfC]
    constructor
    · intro hx
      exact ⟨x, ⟨trivial, hx⟩, rfl⟩
    · rintro ⟨x', ⟨-, hx'⟩, e'⟩
      have := (UI.brg (MF.toFrames F)).injective e'
      subst this
      exact hx'
  rw [e]
  exact (isCompact_univ.prod isCompact_singleton).image (UI.brg (MF.toFrames F)).continuous

theorem exists_open_compact (hS : V.SigOK) (hD : V.IsDefinite) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ IsCompact (U : Set (GA D V)) := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  haveI := ginf_compact F hD
  let fr := MF.toFrames F
  let H : Subgroup (UI.instV fr).Gf :=
    { carrier := (UI.instV fr).Kset
      one_mem' := (Formalism.UG.stabGL (UI.instV fr).Lf).one_mem
      mul_mem' := fun ha hb => (Formalism.UG.stabGL (UI.instV fr).Lf).mul_mem ha hb
      inv_mem' := fun ha => (Formalism.UG.stabGL (UI.instV fr).Lf).inv_mem ha }
  have ho : IsOpen (H : Set (UI.instV fr).Gf) := by
    show IsOpen (UI.instV fr).Kset
    rw [stabilizer_eq_level_subgroup]
    exact (UI.instV fr).topf_open 1 le_rfl
  have hc : IsCompact (H : Set (UI.instV fr).Gf) := Formalism.L2.SG.Closed.AutKCompact_holds (UI.instV fr)
  refine ⟨(Subgroup.prod ⊤ H).map ((UI.brg fr : (UI.instV fr).GA →* GA D V)), ?_, ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_prod, Subgroup.coe_top]
    exact (UI.brg fr).toHomeomorph.isOpenMap _ (isOpen_univ.prod ho)
  · rw [Subgroup.coe_map, Subgroup.coe_prod, Subgroup.coe_top]
    exact (isCompact_univ.prod hc).image (UI.brg fr).continuous

end Formalism.IndefR.Eqv

end
end

