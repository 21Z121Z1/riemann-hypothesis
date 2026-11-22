import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0112
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MovedLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat Formalism.IndefR

variable {D : D7}

theorem hat_hLat (V : HSp D) (g : Bridge.Gf V) :
    (hat D.host.F (Bridge.hLat V g : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA D.host.F D.host.E)) =
      g.1.1.mulVec '' (hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, -, -, h⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) g.1 hfg hsp
  rw [GlobalTheory.RepsCompare.coe_hLat, ← hΛ, h]

theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  apply SetLike.coe_injective
  rw [GlobalTheory.RepsCompare.coe_hLat]
  ext x
  rw [SetLike.mem_coe, ← (hat_rational_points_and_approx D.host.F D.host.E _ _ hfg hsp).1]
  simp [GlobalTheory.AdLat.latOf]

theorem isSelfDualC_hLat (V : HSp D) (g : Bridge.Gf V) : IsSelfDualC V (Bridge.hLat V g) := by
  refine ⟨GlobalTheory.RepsCompare.isLattice_hLat V g, fun v => ?_⟩
  obtain ⟨-, -, hfg, hsp, c2, -, -, gh, gd, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := latOf_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D) V.gramᵀ 1 g.1 hfg hsp c2 gh gd
    one_ne_zero hsd (GlobalTheory.RepsCompare.isUnA_gf V g)
  rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, ← key, ← GlobalTheory.RepsCompare.coe_hLat]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : ∑ i, ∑ j, star (y i) * V.gram i j * v j = ∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change star (y b) * V.gram b a * v a = v a * V.gram b a * star (y b)
    ring
  rw [e, FractionalIdeal.mem_one_iff]

theorem mulVec_mem_hatL (V : HSp D) (g : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (H : ∀ z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V g).1 *ᵥ z ∈ hat D.host.F (Λ' : Set (Fin V.rank → D.host.E)))
    (x : Fin V.rank → EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  have h := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (H _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ x hx))
  convert h using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  rfl

theorem actO_mem (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ z ∈ hat D.host.F (ΛS : Set (Fin S.rank → D.host.E)),
      (finHom S g).1 *ᵥ z ∈ hat D.host.F (ΛS' : Set (Fin S.rank → D.host.E)))
    (hT : ∀ z ∈ hat D.host.F (ΛT : Set (Fin T.rank → D.host.E)),
      (finHom T h).1 *ᵥ z ∈ hat D.host.F (ΛT' : Set (Fin T.rank → D.host.E)))
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈
      latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, actO_rankOne]
    exact rankOne_mem_latO S T ΛS' ΛT' a ha _
      (mulVec_mem_hatL S g ΛS ΛS' hS _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_hatL T h ΛT ΛT' hT _ (pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem fwd (V : HSp D) (g : GA D V) : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
    (finHom V g).1 *ᵥ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat]
  exact ⟨z, hz, rfl⟩

theorem bwd (V : HSp D) (g : GA D V) :
    ∀ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)),
    (finHom V g⁻¹).1 *ᵥ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  change (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) ∈ _
  rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  exact hy

theorem latG_eq (W : HSp D) (k : GA D W) : Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (FWT.fin W k), w = a • v} := by
  have key : ∀ v, Formalism.L2.Pj.finVec W v ∈ Formalism.L2.Pj.gLat W k ↔ v ∈ Bridge.hLat W (FWT.fin W k) := by
    intro v
    rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, Formalism.L2.Pj.gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1]
    exact Iff.rfl
  unfold Formalism.L2.Pj.latG
  simp only [key]

theorem moved_lattices : ∀ (D : D7) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (h : GA D V) (k : GA D W), IsSelfDualC V (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧ IsSelfDualC W (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k)) ∧ (∀ u : WO V W, u ∈ (latO V W (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h) : Set (Fin V.rank → D.host.E)) (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h k u₀) ∧ Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k), w = a • v} ∧ Formalism.IndefR.Bridge.hLat V 1 = ΛV ∧ Formalism.IndefR.Bridge.hLat W 1 = ΛW := by
  intro D V W ΛV ΛW hV hW _ _ h k
  obtain rfl : ΛV = GlobalTheory.Member.latC V := SetLike.coe_injective (hV.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  obtain rfl : ΛW = GlobalTheory.Member.latC W := SetLike.coe_injective (hW.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq W).symm)
  refine ⟨isSelfDualC_hLat V _, isSelfDualC_hLat W _, fun u => ⟨fun hu => ?_, ?_⟩, latG_eq W k, hLat_one V, hLat_one W⟩
  · exact ⟨_, actO_mem V W h⁻¹ k⁻¹ _ _ _ _ (bwd V h) (bwd W k) u hu, (actO_actO_inv V W h k u).symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    exact actO_mem V W h k _ _ _ _ (fwd V h) (fwd W k) u₀ hu

end GlobalTheory.MovedLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVector
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.WordWeight

theorem step {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℝ) (v : V)
    (hv : IsWeight E ν v) (a b : Fin n) :
    IsWeight E (ν + root a b) (E a b v) := by
  intro c
  have h := hE c c a b
  have h2 : E c c (E a b v) = E a b (E c c v) +
      ((if c = a then E c b else 0) - (if b = c then E a c else 0)) v := by
    rw [← h]; simp [Module.End.mul_apply]
  rw [h2, hv c, map_smul]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hbc : b = c
  · subst hca; subst hbc; simp
  · subst hca
    have : ¬ c = b := fun h => hbc h.symm
    simp [this, hbc]
    rw [add_smul, one_smul]
    rfl
  · subst hbc
    simp [hca]
    rw [add_smul, neg_smul, one_smul]
    rfl
  · have : ¬ c = b := fun h => hbc h.symm
    simp [hca, this, hbc]

theorem word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    ∀ (l : List (Fin n × Fin n)) (μ : Fin n → ℝ) (w : V), IsWeight E μ w →
    IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum)
      ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w)
  | [], μ, w, hw => by simpa using hw
  | p :: l, μ, w, hw => by
    have ih := word E hE l μ w hw
    have := step E hE _ _ ih p.1 p.2
    simp only [List.map_cons, List.sum_cons, List.prod_cons, Module.End.mul_apply]
    convert this using 1
    abel

end GlobalTheory.WordWeight

theorem GlobalTheory.wordWeight : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (μ : Fin n → ℝ) (w : V), IsWeight E μ w → ∀ l : List (Fin n × Fin n), IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum) ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro n V _ _ E hE μ w hw l
  exact GlobalTheory.WordWeight.word E hE l μ w hw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftWeight

theorem one_le_aPl_last (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n + 1 = p) :
    1 ≤ aPl D i p τ n := by
  subst hp
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hlt : n < D.R.k + (i : ℕ) := by omega
  have h1 : ¬ n < D.R.k - 1 := by omega
  have h2 : n - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨n - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by simp only; omega)
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) n = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg h1, dif_pos h2, hidx]
  have hg := (D.hc τ).gap_be i
  have hq : ((D.R.k + (i : ℕ) : ℕ) : ℚ) = (n : ℚ) + 1 := by
    rw [← hn]; push_cast; ring
  simp only [aPl, if_pos hlt]
  rw [hlam, hq]
  have hfl : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - ((n : ℚ) + 1 - ((n : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

theorem kapTop_lastPos (D : D7) (i : Fin D.R.m) : (kapTop D i).LastPos := by
  intro τ k hk
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hW := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D τ)
  have hs : ((Wc D i).sig (tauE D τ)).1 = D.R.k + (i : ℕ) := by
    show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = D.R.k + (i : ℕ)
    rw [hW]
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ)
    omega
  have hk' : (k : ℕ) + 1 = D.R.k + (i : ℕ) := by
    have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
    omega
  exact one_le_aPl_last D i τ _ k hs (hk'.trans hs.symm)

end GlobalTheory.LiftWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquiv
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ Γ' G₁ G₂ _ _ _ _ e ι₁ ι₂ θ K₁ K₂ γ δ f φ
  have hprod : (ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom) = (ι₁.prod ι₂).comp e.toMonoidHom := by
    ext x <;> rfl
  have hR : ((ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom)).range = (ι₁.prod ι₂).range := by
    rw [hprod, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
  have hS : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
    intro x
    have h : stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁ ι₂ K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [h]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun a => by simp [Subgroup.mem_comap]))
  unfold pointSum
  simp only [hS]
  rw [hR]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.PointSumConj

theorem exists_conj_iff {G : Type} [Group G] (K : Subgroup G) (a m : G) :
    (∃ k ∈ K, a * k * a⁻¹ = m) ↔ a⁻¹ * m * a ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : a⁻¹ * (a * k * a⁻¹) * a = k := by group
    rw [this]; exact hk
  · intro h
    exact ⟨a⁻¹ * m * a, h, by group⟩

theorem mem_stab {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) (z : Γ) :
    z ∈ stab ι₁ ι₂ K₁ K₂ x ↔ x.1⁻¹ * ι₁ z * x.1 ∈ K₁ ∧ x.2⁻¹ * ι₂ z * x.2 ∈ K₂ := by
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, exists_conj_iff]

theorem finsum_dc_translate {G : Type} [Group G] (H H' K : Subgroup G) (a : G)
    (hH : ∀ h ∈ H, a * h * a⁻¹ ∈ H') (hH' : ∀ h ∈ H', a⁻¹ * h * a ∈ H) (F F' : G → ℂ)
    (hF : ∀ h ∈ H, ∀ k ∈ K, ∀ x, F (h * x * k) = F x) (hF' : ∀ x, F' (a * x) = F x) :
    ∑ᶠ q : DoubleCoset.Quotient (H' : Set G) (K : Set G), F' (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G), F (Quotient.out q) := by
  have key : ∀ x, F' (Quotient.out (DoubleCoset.mk H' K (a * x))) = F x := by
    intro x
    obtain ⟨h', hh', k, hk, he⟩ := (DoubleCoset.eq H' K _ _).1
      (DoubleCoset.out_eq' H' K (DoubleCoset.mk H' K (a * x))).symm
    rw [he]
    have : h' * (a * x) * k = a * ((a⁻¹ * h' * a) * x * k) := by group
    rw [this, hF', hF _ (hH' _ hh') _ hk]
  refine (finsum_eq_of_bijective (fun q : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    DoubleCoset.mk H' K (a * Quotient.out q)) ⟨?_, ?_⟩ (fun q => (key _).symm)).symm
  · intro q₁ q₂ h
    obtain ⟨h', hh', k, hk, he⟩ := (DoubleCoset.eq H' K _ _).1 h
    rw [← DoubleCoset.out_eq' H K q₁, ← DoubleCoset.out_eq' H K q₂]
    refine (DoubleCoset.eq H K _ _).2 ⟨a⁻¹ * h' * a, hH' _ hh', k, hk, ?_⟩
    have : Quotient.out q₂ = a⁻¹ * (a * Quotient.out q₂) := by group
    rw [this, he]; group
  · intro q'
    refine ⟨DoubleCoset.mk H K (a⁻¹ * Quotient.out q'), ?_⟩
    obtain ⟨h, hh, k, hk, he⟩ := (DoubleCoset.eq H K _ _).1
      (DoubleCoset.out_eq' H K (DoubleCoset.mk H K (a⁻¹ * Quotient.out q'))).symm
    simp only
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' H' K q']
    exact (DoubleCoset.eq H' K _ _).2 ⟨(a * h * a⁻¹)⁻¹, H'.inv_mem (hH _ hh), k⁻¹, K.inv_mem hk, by group⟩

end GlobalTheory.PointSumConj

namespace GlobalTheory.PointSumConj

theorem conj_mem_iff {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) (m : G) :
    k⁻¹ * m * k ∈ K ↔ m ∈ K := by
  rw [Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk)]

theorem card_stab_translate {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (y : Γ) (x k : G₁ × G₂) (hk : k ∈ K₁.prod K₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ ((ι₁ y, ι₂ y) * x * k)) = Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
  rw [Subgroup.mem_prod] at hk
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj y).toEquiv fun z => ?_)).symm
  simp only [SetLike.mem_coe, mem_stab, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
    Prod.fst_mul, Prod.snd_mul, map_mul, map_inv]
  have e1 : (ι₁ y * x.1 * k.1)⁻¹ * (ι₁ y * ι₁ z * (ι₁ y)⁻¹) * (ι₁ y * x.1 * k.1) =
      k.1⁻¹ * (x.1⁻¹ * ι₁ z * x.1) * k.1 := by group
  have e2 : (ι₂ y * x.2 * k.2)⁻¹ * (ι₂ y * ι₂ z * (ι₂ y)⁻¹) * (ι₂ y * x.2 * k.2) =
      k.2⁻¹ * (x.2⁻¹ * ι₂ z * x.2) * k.2 := by group
  rw [e1, e2, conj_mem_iff K₁ hk.1, conj_mem_iff K₂ hk.2]

theorem stab_conj {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (g₁ : G₁) (g₂ : G₂) (x : G₁ × G₂) :
    stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) K₁ K₂
      ((g₁⁻¹, g₂⁻¹) * x) = stab ι₁ ι₂ K₁ K₂ x := by
  ext z
  simp only [mem_stab, Prod.fst_mul, Prod.snd_mul, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (g₁⁻¹ * x.1)⁻¹ * (g₁⁻¹ * ι₁ z * g₁⁻¹⁻¹) * (g₁⁻¹ * x.1) = x.1⁻¹ * ι₁ z * x.1 := by group
  have e2 : (g₂⁻¹ * x.2)⁻¹ * (g₂⁻¹ * ι₂ z * g₂⁻¹⁻¹) * (g₂⁻¹ * x.2) = x.2⁻¹ * ι₂ z * x.2 := by group
  rw [e1, e2]

theorem pointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ G₁ G₂ _ _ _ ι₁ ι₂ θ K₁ K₂ γ g₁ δ g₂ f φ hf hφ hγ hδ
  unfold pointSum
  refine finsum_dc_translate (ι₁.prod ι₂).range
    (((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁).prod ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)).range
    (K₁.prod K₂) (g₁⁻¹, g₂⁻¹) ?_ ?_
    (fun x => ((Nat.card (stab ι₁ ι₂ K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2)))
    (fun x => ((Nat.card (stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)
      K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * (g₁⁻¹ * γ * g₁) * x.1) * φ (x.2⁻¹ * (g₂⁻¹ * δ * θ g₂) * θ x.2))) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply]
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply] <;> group
  · rintro _ ⟨y, rfl⟩ k hk x
    have hk' := (Subgroup.mem_prod).1 hk
    simp only [MonoidHom.prod_apply] at *
    rw [card_stab_translate ι₁ ι₂ K₁ K₂ y x k hk]
    congr 2
    · have e : ((ι₁ y, ι₂ y) * x * k).1⁻¹ * γ * ((ι₁ y, ι₂ y) * x * k).1 =
          k.1⁻¹ * (x.1⁻¹ * ((ι₁ y)⁻¹ * γ * ι₁ y) * x.1) * k.1 := by simp only [Prod.fst_mul]; group
      have e' : (ι₁ y)⁻¹ * γ * ι₁ y = γ := by rw [mul_assoc, ← hγ y]; group
      rw [e, e', hf _ hk'.1]
    · have e : ((ι₁ y, ι₂ y) * x * k).2⁻¹ * δ * θ ((ι₁ y, ι₂ y) * x * k).2 =
          k.2⁻¹ * (x.2⁻¹ * ((ι₂ y)⁻¹ * δ * θ (ι₂ y)) * θ x.2) * θ k.2 := by
        simp only [Prod.snd_mul, map_mul]; group
      have e' : (ι₂ y)⁻¹ * δ * θ (ι₂ y) = δ := by rw [mul_assoc, ← hδ y]; group
      rw [e, e', hφ _ hk'.2]
  · intro x
    rw [stab_conj]
    congr 2
    · congr 1; simp only [Prod.fst_mul]; group
    · congr 1; simp only [Prod.snd_mul, map_mul, map_inv]; group

end GlobalTheory.PointSumConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalence
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem rel_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  intro p _ G
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, ?_⟩
    · simp [sh_one']
    · simp
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        rw [← sh_mul', Units.inv_mul, sh_one']
      rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
        inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, sh_mul']
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]
    · rw [hγ', hγ]; group

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrime
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem exists_integral_inverse_lieVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  intro E _ _ _ H Dw l Xo c _ p _ T io X y Ch hp inst
  have hbij := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose σV hσV using fun τ : E →+* ℂ =>
    GlobalTheory.PowGerm.exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hι : ∀ τ a, X.ι (σV τ a) = embO io X τ a := fun τ a => X.ints.hom_inj (by
    rw [algebraMap_embO, ← X.comp, hσV']; rfl)
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit (σV τ a - σV τ' a) := by
    intro τ τ' hne
    have h1 : red io X τ ≠ red io X τ' := fun h => hne (hbij.1 h)
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
    refine ⟨a, ?_⟩
    have := X.ι_local
    refine (isUnit_map_iff X.ι _).1 ?_
    rw [map_sub, hι, hι]
    by_contra hu
    apply ha
    rw [← sub_eq_zero]
    show residue X.O _ - residue X.O _ = 0
    rw [← map_sub, residue_eq_zero_iff]
    exact (mem_maximalIdeal _).2 hu
  have hex : ∃ lam : Lt1 Dw → Fin (chD Ch.ch) → T.V, ∀ l l', ∑ s, lam l s * Ch.uvecT l' s = if l = l' then 1 else 0 := by
    classical
    obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD Ch.ch)
      (fun a => Matrix.of fun m j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a m))
      (E →+* ℂ) Dw.mult (fun τ a => σV τ a) Ch.uvecT hsep
      (fun a ℓ => ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a _ (hσV' _ _)) (fun τ => by
        obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
        exact GlobalTheory.PowGerm.exists_dual_of_extends (fun i => Ch.uvecT ⟨τ, i⟩) w emb hw hb)
    exact ⟨lam, fun l l' => by convert hlam l l'⟩
  obtain ⟨lam, hlam⟩ := hex
  have h1 : (Matrix.of fun ℓ e => jX X (lam ℓ e)) * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 := by
    ext ℓ ℓ'
    have h := congrArg (jX X) (hlam ℓ ℓ')
    rw [map_sum] at h
    simp only [map_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, lieVec]
    rw [h]
    split_ifs
    · exact map_one _
    · exact map_zero _
  refine ⟨Matrix.of fun ℓ e => jX X (lam ℓ e), fun a b => isIntV_jX X _, h1, ?_⟩
  have e : Lt1 Dw ≃ Fin (chD Ch.ch) := Fintype.equivFinOfCardEq (GlobalTheory.IntChartCheck.dim_eq Ch).symm
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 h1

end GlobalTheory.PrimePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdealStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_lift_congruent_mod_ideal : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  first | exact @GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul | exact GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul | (intros; apply GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul <;> assumption)
end

