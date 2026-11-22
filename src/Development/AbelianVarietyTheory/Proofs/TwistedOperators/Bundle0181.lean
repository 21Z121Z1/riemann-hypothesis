import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeSize

theorem k_pow_le_g {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (i : Fin 2) : D.R.k ^ 8 ≤ D.host.g i := by
  obtain ⟨Y, h1, -, -, h4⟩ := P.g_Y
  have hL : 0 ≤ L.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ≤ D.R.k * L.sc.b := le_mul_of_one_le_right hk hb
  have h3 : (D.R.k : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ hk h2 8
  have : (D.R.k : ℝ) ^ 8 ≤ D.host.g i := h3.trans (h1.trans (h4 i).1)
  exact_mod_cast this

theorem typePrime_large_and_ok : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2,
    Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧
      GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  intro D L P i
  have hg := k_pow_le_g P i
  have hE : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have he := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) he
  have hf := D.R.f_le_k
  have hfo : D.R.f = 2 * D.R.ord := rfl
  have ho : 2 ^ D.R.e ≤ D.R.ord := Nat.le_of_dvd D.R.ord_pos D.R.toFrame.two_pow_dvd_ord
  have hm := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hk8 : 8 ≤ D.R.k := by omega
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hE' : Module.finrank ℚ D.host.E ≤ 2 * D.R.k := by
    have h2f : D.R.f = 2 * D.R.ord := rfl
    have hfk : D.R.f ≤ D.R.k := hf
    omega
  have hk6 : 8 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk8 6
  have hk2 : 8 ^ 2 ≤ D.R.k ^ 2 := Nat.pow_le_pow_left hk8 2
  have hpow : 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 8 := by
    calc 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 6 * D.R.k ^ 2 := Nat.mul_le_mul_right _ hk6
      _ = D.R.k ^ 8 := by ring
  have hprod : Module.finrank ℚ D.host.E * D.R.r ≤ 4 * D.R.k ^ 2 := by
    calc Module.finrank ℚ D.host.E * D.R.r ≤ (2 * D.R.k) * (2 * D.R.k) := Nat.mul_le_mul hE' hr
      _ = 4 * D.R.k ^ 2 := by ring
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hb := D.host.qd_big.1
  refine ⟨by omega, hq, hd, by omega, by omega, by omega, ?_, ?_, by omega⟩
  · have h1 : 5 * 1 ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr1
    have h2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
    exact le_max_of_le_left (by omega)
  · have hc := D.ntypes.g_cond i
    have hdvd : 16 * D.host.q * D.host.d ∣ D.host.QS * D.host.q * D.host.d := by
      have h16 : 16 ∣ D.host.QS := (pow_dvd_pow 2 (by omega : 4 ≤ D.R.e + 2)).trans D.host.tower_dvd
      exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h16 _) _
    refine hdvd.trans ⟨D.host.g i / (D.host.QS * D.host.q * D.host.d), ?_⟩
    have := Nat.div_add_mod (D.host.g i) (D.host.QS * D.host.q * D.host.d)
    omega

end GlobalTheory.TypePrimeSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree.AdelCls

open GlobalTheory.Mass

theorem dc_iff {G H : Type} [Group G] [Group H] (f : G →* H) (Γ A L N : Subgroup G) (Q K : Subgroup H)
    (hQ : Γ.map f = Q) (hA : ∀ x, ∃ h ∈ A, f h = x) (hL : ∀ κ, κ ∈ L ↔ κ ∈ A ∧ f κ ∈ K)
    (hN : ∀ h, f h = 1 ↔ h ∈ N) (h h' : G) :
    (∃ x ∈ Q, ∃ k ∈ K, f h' = x * f h * k) ↔ ∃ γ ∈ Γ, ∃ κ ∈ L, ∃ k ∈ N, h' = γ * h * κ * k := by
  constructor
  · rintro ⟨x, hx, k, hk, e⟩
    rw [← hQ] at hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨κ, hκA, rfl⟩ := hA k
    refine ⟨γ, hγ, κ, (hL κ).2 ⟨hκA, hk⟩, (γ * h * κ)⁻¹ * h', (hN _).1 ?_,
      (mul_inv_cancel_left (γ * h * κ) h').symm⟩
    simp only [map_mul, map_inv, e, inv_mul_cancel]
  · rintro ⟨γ, hγ, κ, hκ, k, hk, rfl⟩
    refine ⟨f γ, ?_, f κ, ((hL κ).1 hκ).2, ?_⟩
    · rw [← hQ]
      exact Subgroup.mem_map_of_mem f hγ
    · rw [map_mul, map_mul, map_mul, (hN k).2 hk, mul_one]

variable {D : D7}

theorem finU_eq (V : HSp D) {π : GA D V →* HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) (h : GA D V) :
    finU V h = swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) := by
  apply Subtype.ext
  rw [coe_finU, coe_swapPts, hπ h]
  rfl

theorem finU_eq_one_iff (V : HSp D) (h : GA D V) : finU V h = 1 ↔ h ∈ GinfC V := by
  have hs : Function.Injective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective
  have hb : Function.Injective
      (Formalism.UG.bc (swapAE D) : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →* GL (Fin V.rank) (EAf D)) :=
    Units.map_injective (Matrix.map_injective hs)
  rw [← OneMemClass.coe_eq_one, coe_finU, GinfC, MonoidHom.mem_ker]
  change Formalism.UG.bc (swapAE D) (finHom V h) = 1 ↔ finHom V h = 1
  exact map_eq_one_iff _ hb

theorem exists_fin (V : HSp D) (x : UA D.sp.cm V.gram) : ∃ h ∈ GfC V, finU V h = x := by
  obtain ⟨hsp, hex⟩ := parts_spec (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram
  obtain ⟨y, rfl⟩ := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x
  obtain ⟨g, g1, g2⟩ := hex 1 (HA.mat _ _ _ y)
  have hg : g ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := by
    refine (hsp g).2 ⟨?_, ?_⟩
    · rw [g1]
      exact one_mem _
    · rw [g2]
      exact (y : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).2
  refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 g1, ?_⟩
  apply Subtype.ext
  rw [coe_swapPts, ← g2]
  rfl

theorem mem_levA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (κ : GA D V) :
    κ ∈ levA V K ↔ κ ∈ GfC V ∧ finU V κ ∈ K.subgroupOf (UA D.sp.cm V.gram) := by
  simp only [levA, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_finU]

theorem map_rat (V : HSp D) : (GQ V).map (finU V) = UQ D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  have e : finU V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π :=
    MonoidHom.ext fun h => finU_eq V hπ h
  have h1 : (GQ V).map π = ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := hπ.map_ratIn
  rw [e, ← Subgroup.map_map, h1]
  exact map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram

theorem rat_mem (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) : finU V γ ∈ UQ D.sp.cm V.gram := by
  rw [← map_rat V]
  exact Subgroup.mem_map_of_mem _ hγ

theorem rat_inj (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (e : finU V γ = 1) : γ = 1 := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  rw [finU_eq V hπ, MulEquiv.map_eq_one_iff] at e
  exact hπ.injOn (SetLike.mem_coe.2 hγ) (SetLike.mem_coe.2 (Subgroup.one_mem _)) (by rw [e, map_one])

theorem adelic_classes : ∀ (D : D7) (V : HSp D), (∀ x : UA D.sp.cm V.gram, ∃ h ∈ GfC V, finU V h = x) ∧ (∀ γ ∈ GQ V, finU V γ ∈ UQ D.sp.cm V.gram) ∧ (∀ x ∈ UQ D.sp.cm V.gram, ∃ γ ∈ GQ V, finU V γ = x) ∧ (∀ γ ∈ GQ V, finU V γ = 1 → γ = 1) ∧ ∀ (K : Subgroup (GL (Fin V.rank) (EAf D))) (h h' : GA D V), clsA V K h = clsA V K h' ↔ ∃ γ ∈ GQ V, ∃ κ ∈ levA V K, ∃ k ∈ GinfC V, h' = γ * h * κ * k := by
  intro D V
  refine ⟨exists_fin V, rat_mem V, fun x hx => ?_, rat_inj V, fun K h h' => ?_⟩
  · rw [← map_rat V] at hx
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 hx
    exact ⟨γ, hγ, e⟩
  · first
      | rw [clsA, clsA, Quotient.eq'', DoubleCoset.rel_iff]
      | (show DoubleCoset.mk _ _ (finU V h) = DoubleCoset.mk _ _ (finU V h') ↔ _
         rw [DoubleCoset.eq])
    exact dc_iff (finU V) (GQ V) (GfC V) (levA V K) (GinfC V) (UQ D.sp.cm V.gram)
      (K.subgroupOf (UA D.sp.cm V.gram)) (map_rat V) (exists_fin V) (mem_levA V K) (finU_eq_one_iff V) h h'

end GlobalTheory.DefFree.AdelCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrMove

open GlobalTheory.SplitHecke GlobalTheory.AdelicLatMove

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  show _ * (x + y) * _ = _ * x * _ + _ * y * _
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

private lemma isHalf_iff_smul_eq {e : AE D} (u : WO S T) : IsHalf e u ↔ e • u = u := by
  unfold IsHalf
  constructor
  · intro hu
    exact Matrix.ext fun i j => by simpa [Matrix.smul_apply] using hu i j
  · intro hu i j
    simpa [Matrix.smul_apply] using congrFun (congrFun hu i) j

private lemma isHalf_actO_twisted_operators {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [isHalf_iff_smul_eq] at hu ⊢
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]

private lemma actO_inv_actO_twisted_operators (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (u : WO S T) :
    IsHalf e (actO S T g h u) ↔ IsHalf e u := ⟨fun hu => by simpa only [actO_inv_actO_twisted_operators] using isHalf_actO_twisted_operators g⁻¹ h⁻¹ hu, isHalf_actO_twisted_operators g h⟩

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨hsupp, k, hk, hper, hden⟩ := hΨ
  refine ⟨fun t ht => (isHalf_actO_iff g h t).1 (hsupp _ ht), k, hk, ?_, fun t ht => ?_⟩
  · intro u hu hue t
    show Ψ (actO S T g h (t + k • u)) = Ψ (actO S T g h t)
    rw [actO_add, actO_nsmul]
    exact hper _ ((hΛ u).1 hu) ((isHalf_actO_iff g h u).2 hue) _
  · rw [hΛ, actO_nsmul]
    exact hden _ ht

theorem halfInd_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) : halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have hc : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
    rw [← hΛ t, isHalf_actO_iff]
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos (hc.2 ht), if_pos ht]
  · rw [if_neg (fun h' => ht (hc.1 h')), if_neg ht]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  unfold heisO
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_move {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D}
    {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf a Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) {c : ℂ} (hc : c ≠ 0) (h0 : om (g, h) f₀ = c • f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀
      (c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))) := by
  obtain ⟨htr, hmod, hvac⟩ := hTm
  have hSB : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf a Λ fun t => Φ (actO S T g h t) := fun Φ hΦ => isSBHalf_comp hΛ hΦ
  have hback : ∀ w : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa only [inv_inv] using actO_inv_actO g⁻¹ h⁻¹ w
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · have hx' : IsHalf a (actO S T g⁻¹ h⁻¹ x) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hx)
    have e1 : Tm (fun s => Φ (actO S T g h s + x)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ x) (Tm fun s => Φ (actO S T g h s)) := by
      have := htr _ (hSB Φ hΦ) _ hx'
      simpa only [actO_add, hback] using this
    show c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s + x))) =
      heisO ψ S T x (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e1, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have hy' : IsHalf (cA D a) (actO S T g⁻¹ h⁻¹ y) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hy)
    have e2 : Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ y) (Tm fun s => Φ (actO S T g h s)) := by
      rw [← hmod _ (hSB Φ hΦ) _ hy']
      congr 1
      funext s
      rw [← symplO_actO S T g h s (actO S T g⁻¹ h⁻¹ y), hback]
    show c⁻¹ • om (g, h) (Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s))) =
      heisO ψ S T y (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e2, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have e3 : (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s)) = (1 : ℂ) • halfInd a Λ := by
      funext s
      simp only [Pi.smul_apply, halfInd_comp hΛ]
    show c⁻¹ • om (g, h) (Tm (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s))) = f₀
    rw [e3, hvac, h0, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem smul_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ g h, (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ (f₀ Φ f : WO S T → ℂ) (c d : ℂ), IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f → c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g h x) = d * Φ x) → d • om (g, h) f = c • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT a ha ha0 g h hΛ f₀ Φ f c d hf₀ hth hc h0 hΦ
  obtain ⟨⟨Tm, hTm⟩, huniq⟩ := hth
  have hfT : f = Tm Φ := huniq Tm hTm
  have hthT := fun Ψ hΨ =>
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hS hT a ha ha0 f₀ hf₀ Tm hTm Ψ hΨ
  have hf' := huniq _ (isPlaceModel_move hW hΛ hTm hthT hc h0)
  have hcomp : (fun x => Φ (actO S T g h x)) = d • Φ := by
    funext x
    simp only [hΦ, Pi.smul_apply, smul_eq_mul]
  have key : f = c⁻¹ • (d • om (g, h) f) := by
    refine hf'.trans ?_
    show c⁻¹ • om (g, h) (Tm (fun x => Φ (actO S T g h x))) = c⁻¹ • (d • om (g, h) f)
    rw [hcomp, map_smul, map_smul, ← hfT]
  calc d • om (g, h) f = c • (c⁻¹ • (d • om (g, h) f)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = c • f := by rw [← key]

end GlobalTheory.SchrMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitution
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrodSubst

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

private lemma isSBHalf_psi_mul_halfInd {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : y ∈ half S T (cA D e)) {m : ℕ} (hm : 0 < m) (hmy : m • y ∈ Λ) :
    IsSBHalf e Λ (fun t => ψ (symplO S T t y) * halfInd e Λ t) := by
  have h0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  unfold IsSBHalf at h0 ⊢
  obtain ⟨hsupp, k, hk, hinv, hlat⟩ := h0
  have hχ := GlobalTheory.PlaceModel.isBichar_symplO S T ψ
  refine ⟨fun t ht => hsupp t (right_ne_zero_of_mul ht), m * k, Nat.mul_pos hm hk, ?_, ?_⟩
  · intro u hu hue t
    have huh : u ∈ half S T e := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hue
    have hmu : IsHalf e (m • u) := (GlobalTheory.PlaceModel.isHalf_iff S T).2 ((half S T e).nsmul_mem huh m)
    have hI : halfInd e Λ (t + (m * k) • u) = halfInd e Λ t := by
      rw [mul_comm, ← smul_smul]
      exact hinv (m • u) (Λ.nsmul_mem hu m) hmu t
    have hone : ψ (symplO S T ((m * k) • u) y) = 1 := by
      have hs := hχ.nsmul m (k • u) y
      rw [← smul_smul, hs]
      exact hLL' (k • u) ⟨Λ.nsmul_mem hu k, (half S T e).nsmul_mem huh k⟩ (m • y)
        ⟨hmy, (half S T (cA D e)).nsmul_mem hy m⟩
    have hsplit := hχ.left t ((m * k) • u) y
    beta_reduce
    rw [hI, hsplit, hone, mul_one]
  · intro t ht
    rw [← smul_smul]
    exact Λ.nsmul_mem (hlat t (right_ne_zero_of_mul ht)) m

theorem placeModel_wave {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁) {x y : WO S T} (hx : IsHalf e x)
    (hy' : IsHalf (cA D e) y) :
    T₁ (wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y) =
      heisO ψ S T x (heisO ψ S T y f₀) := by
  obtain ⟨m, hm, hmy⟩ := hden y ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy')
  have hΦ0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  have hΨ := isSBHalf_psi_mul_halfInd hLL' ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy') hm hmy
  have hwave : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
      fun t => ψ (symplO S T (t + x) y) * halfInd e Λ (t + x) := by
    funext t
    simp only [GlobalTheory.PlaceModel.wave, GlobalTheory.PlaceModel.halfInd_eq_ind]
  have hvac : T₁ (halfInd e Λ) = f₀ := by simpa using h₁.vac
  rw [hwave, h₁.trans _ hΨ x hx, h₁.modul _ hΦ0 y hy', hvac]

theorem wave_actO (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (x y : WO S T) :
    (fun t => wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y (actO S T g⁻¹ h⁻¹ t)) =
      wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) (actO S T g h x) (actO S T g h y) := by
  funext t
  have ht : actO S T g h (actO S T g⁻¹ h⁻¹ t) = t := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
  have hadd : t + actO S T g h x = actO S T g h (actO S T g⁻¹ h⁻¹ t + x) := by
    have := map_add (GlobalTheory.SplitHecke.actAdd S T g h) (actO S T g⁻¹ h⁻¹ t) x
    change actO S T g h (actO S T g⁻¹ h⁻¹ t + x) = actO S T g h (actO S T g⁻¹ h⁻¹ t) + actO S T g h x at this
    rw [this, ht]
  have hhalf : ∀ w : WO S T, actO S T g h w ∈ half S T e ↔ w ∈ half S T e := by
    intro w
    simp only [← GlobalTheory.PlaceModel.isHalf_iff]
    constructor
    · intro hw
      simpa [GlobalTheory.SplitHecke.actO_inv_actO] using GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hw
    · exact GlobalTheory.SplitHecke.isHalf_actO g h
  have hmem : ∀ w : WO S T, actO S T g h w ∈ Λ ⊓ half S T e ↔ w ∈ Λ ⊓ half S T e := by
    intro w
    simp only [AddSubgroup.mem_inf, hhalf, ← hΛ w]
  simp only [GlobalTheory.PlaceModel.wave]
  rw [hadd, GlobalTheory.SplitHecke.symplO_actO]
  simp only [GlobalTheory.PlaceModel.ind]
  by_cases hw : actO S T g⁻¹ h⁻¹ t + x ∈ Λ ⊓ half S T e
  · rw [if_pos hw, if_pos ((hmem _).2 hw)]
  · rw [if_neg hw, if_neg (fun hw' => hw ((hmem _).1 hw'))]

theorem om_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun _ => True)) → om (g, h) f₀ = c • f₀ → ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun x => Φ (actO S T g⁻¹ h⁻¹ x) := by
  intro D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hth hTm g h c hΛ hc Φ hΦ
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hψ : IsCharAF D.host.F ψ := by
    unfold IsStdChar at hstd
    exact hstd.1
  have hdual := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hstd hS hT).1
  have hsm : ∀ w : AE D, w * w = w → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      w • u ∈ (latO S T ΛS ΛT fun _ => True) := by
    intro w hw u hu
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T ΛS ΛT (fun _ => True) w ?_ u hu
    exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hw])
  have hfm := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True)
  have hnm : ∀ t : WO S T, t.map (infPart D) = 0 → ∃ k : ℕ, 0 < k ∧ k • t ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun t ht => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 t ht
  generalize (latO S T ΛS ΛT fun _ => True) = Λ at hdual hsm hfm hnm hTm hΛ hΦ ⊢
  have hcA : cA D a * cA D a = cA D a := by rw [← map_mul, ha]
  have hinf' : infPart D (cA D a) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hLL : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1 := by
    intro u hu y hy
    rw [AddSubgroup.mem_inf] at hu hy
    exact (hdual u (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hden : ∀ y ∈ half S T (cA D a), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ := fun y hy =>
    hnm y (GlobalTheory.PlaceDatum.infPart_of_half hinf' ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hy))
  have hXd : ∀ x ∈ half S T a, (∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) →
      x ∈ Λ ⊓ half S T a := by
    intro x hx hxy
    refine AddSubgroup.mem_inf.2 ⟨?_, hx⟩
    refine (hdual x (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hx))).2 ?_
    intro u' hu'
    have hmem : cA D a • u' ∈ Λ ⊓ half S T (cA D a) := by
      refine AddSubgroup.mem_inf.2 ⟨hsm _ hcA u' hu', ?_⟩
      rw [GlobalTheory.PlaceModel.mem_half, smul_smul, hcA]
    have heq : symplO S T x u' = symplO S T x (cA D a • u') := by
      rw [← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 hx]
    rw [heq]
    exact hxy _ hmem
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T a, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T a, t = r + k • u := by
    intro k hk
    obtain ⟨R, hR, hRt⟩ := hfm k hk
    refine ⟨(fun r => a • r) '' R, hR.image _, ?_⟩
    intro t ht
    rw [AddSubgroup.mem_inf] at ht
    obtain ⟨r, hr, u, hu, rfl⟩ := hRt t ht.1
    refine ⟨a • r, Set.mem_image_of_mem _ hr, a • u, AddSubgroup.mem_inf.2 ⟨hsm a ha u hu, ?_⟩, ?_⟩
    · rw [GlobalTheory.PlaceModel.mem_half, smul_smul, ha]
    · have h2 := (GlobalTheory.PlaceModel.mem_half S T).1 ht.2
      rw [smul_add, smul_comm a k u] at h2
      exact h2.symm
  have htf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk =>
    Function.LeftInverse.injective (g := fun t : WO S T => incA D (k : D.host.E)⁻¹ • t)
      (fun t => GlobalTheory.PlaceModel.inv_smul_nsmul S T hk t)
  have hspan : Φ ∈ GlobalTheory.PlaceModel.waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T a)
      (half S T (cA D a)) (Λ ⊓ half S T a) := by
    unfold IsSBHalf at hΦ
    obtain ⟨hsupp, k, hk, hinv, hlat⟩ := hΦ
    refine GlobalTheory.PlaceDatum.mem_waveSpan (L' := Λ ⊓ half S T (cA D a)) (GlobalTheory.PlaceModel.isBichar_symplO S T ψ)
      inf_le_right inf_le_right hLL hXd (fun k hk x hx => GlobalTheory.PlaceModel.half_div S T a k hk x hx)
      (fun k hk y hy => GlobalTheory.PlaceModel.half_div S T (cA D a) k hk y hy) htf hfin Φ
      (fun t ht => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k hk ?_ ?_
    · intro u hu t
      rw [AddSubgroup.mem_inf] at hu
      exact hinv u hu.1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2) t
    · intro t ht
      exact AddSubgroup.mem_inf.2 ⟨hlat t ht,
        (half S T a).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k⟩
  clear hΦ
  unfold GlobalTheory.PlaceModel.waveSpan at hspan
  induction hspan using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hΨ
    have hxH : IsHalf a x := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hx
    have hyH : IsHalf (cA D a) y := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hy
    have hthy : IsThetaFunO ψ S T (heisO ψ S T y f₀) :=
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ (GlobalTheory.PlaceDatum.infPart_of_half hinf' hyH) hth
    rw [placeModel_wave hLL hden hTm hxH hyH, hW.om_heis g h x _ hthy, hW.om_heis g h y f₀ hth, hc,
      GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul, wave_actO ψ a hΛ x y,
      placeModel_wave hLL hden hTm (GlobalTheory.SplitHecke.isHalf_actO g h hxH) (GlobalTheory.SplitHecke.isHalf_actO g h hyH)]
  | zero =>
    rw [show (fun x => (0 : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x)) = 0 from rfl]
    simp only [map_zero, smul_zero]
  | add Ψ₁ Ψ₂ _ _ ih₁ ih₂ =>
    rw [show (fun x => (Ψ₁ + Ψ₂) (actO S T g⁻¹ h⁻¹ x)) =
      (fun x => Ψ₁ (actO S T g⁻¹ h⁻¹ x)) + (fun x => Ψ₂ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_add, ih₁, ih₂, smul_add]
  | smul r Ψ _ ih =>
    rw [show (fun x => (r • Ψ) (actO S T g⁻¹ h⁻¹ x)) = r • (fun x => Ψ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_smul, ih]
    exact smul_comm r c _

end GlobalTheory.SchrodSubst

end
end

