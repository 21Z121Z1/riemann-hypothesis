import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnitConjugateNormTwoPowerTwoAdic

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlLeParams
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.AlTop

theorem al_le_rowLen_sub {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (t : HH D) (ht : t ∈ D.host.TT) :
    al L (aL L) t ≤ (((nuD D u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD D u j (false, t)).rowLen 1 : ℕ) : ℝ) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hz : IsTopPl D (false, t) := ⟨rfl, ht⟩
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl L u j hj (false, t) hz
  have hwe : wPl D (j + 1) (false, t) = (((D.hcW u (tauPl D (false, t))).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  obtain ⟨-, h4⟩ := L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hS := L.Sc_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1,
    RowWeightLemmas.nuRow_head D u j hj _ 1 (by omega), hwe]
  unfold al cG kaJ Ranks.N
  push_cast
  linarith

theorem al_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, al (Fm.L x i) (aL (Fm.L x i)) t ≤ (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) :=
  fun Fm => ⟨0, fun x _ _ i u j hj t ht => al_le_rowLen_sub (Fm.L x i) u j hj t ht⟩

end GlobalTheory.AlTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLe
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.CapBound

theorem row_le (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr1 : r ≤ 1)
    (hr : r < D.R.k) :
    (((nuD D u j z).rowLen r : ℕ) : ℝ) ≤
      wPl D (j + 1) z - kaJ D (j + 1) + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  rw [nuRowOK D u j hj z r, if_pos h2, RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  unfold kaJ Ranks.N
  push_cast
  linarith

theorem cap_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.fill_eq_wPl Fm
  refine ⟨x0, fun x hx hx1 i u j hj z => ?_⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hx0 x hx hx1 i j hj z]
  split_ifs with hz
  · have h1 := row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx1 i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

end GlobalTheory.CapBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresBasic

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem coef_inv (f : S.Forms) (c : S.Cl) (g : stab ι J (P.y c)) :
    (χ (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef ((f : S.Cl → S.V) c)) = P.coef ((f : S.Cl → S.V) c) := by
  obtain ⟨g, rfl⟩ := (P.stabI c).surjective g
  rw [← P.coef_act, f.2 c g]

theorem ext_dec (f : S.Forms) (γ : Γ) (c : S.Cl) (k : J) :
    P.ext (f : S.Cl → S.V) (ι γ * P.y c * k) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have hs := P.dec_spec (ι γ * P.y c * k)
  have hc : P.decC (ι γ * P.y c * k) = c :=
    (P.reps (ι γ * P.y c * k)).unique ⟨_, _, hs⟩ ⟨γ, k, rfl⟩
  unfold ClassPres.ext
  rw [hc] at hs ⊢
  generalize P.decG (ι γ * P.y c * k) = γ' at hs ⊢
  generalize P.decK (ι γ * P.y c * k) = k' at hs ⊢
  have e : (P.y c)⁻¹ * ι (γ⁻¹ * γ') * P.y c = (k : G) * (k' : G)⁻¹ := by
    have h2 : ι γ' = ι γ * P.y c * k * (k' : G)⁻¹ * (P.y c)⁻¹ := by rw [hs]; group
    rw [map_mul, map_inv, h2]; group
  have hm : γ⁻¹ * γ' ∈ stab ι J (P.y c) := by
    rw [mem_stab, e]; exact J.mul_mem k.2 (J.inv_mem k'.2)
  have hk : stabK ι (⟨_, hm⟩ : stab ι J (P.y c)) = k' * k⁻¹ := by
    apply Subtype.ext
    simp only [stabK]
    rw [e]; simp
  have hi := coef_inv P f c ⟨_, hm⟩
  rw [hk] at hi
  conv_rhs => rw [← hi]
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul]
  congr 1
  · rw [map_mul, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, inv_mul_cancel_right]
  · simp

theorem ext_y (f : S.Forms) (c : S.Cl) :
    P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c) := by
  have := ext_dec P f 1 c 1
  simpa using this

theorem extMem : P.ExtMem := by
  intro f γ h k
  obtain ⟨c, ⟨γ', k', rfl⟩, -⟩ := P.reps h
  have e : ι γ * (ι γ' * P.y c * k') * k = ι (γ * γ') * P.y c * (k' * k : J) := by
    simp [mul_assoc]
  rw [e, ext_dec, ext_dec, map_mul, map_mul, map_smul, smul_smul, Units.val_mul, mul_comm]
  rfl

theorem isom : P.Isom := by
  intro f f'
  unfold adInner CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ext_y, ext_y, P.coef_pair, map_mul, map_inv₀, map_natCast, CSD.wt,
    ← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card]

def bW : Module.Basis S.ιV ℂ W := Module.Basis.mk P.coef_li (by rw [P.coef_span])

theorem bW_apply (j : S.ιV) : bW P j = P.coef (S.bV j) := by simp [bW]

theorem repr_coef (x : S.V) (j : S.ιV) : (bW P).repr (P.coef x) j = σ (S.bV.repr x j) := by
  have : P.coef x = ∑ i, σ (S.bV.repr x i) • bW P i := by
    conv_lhs => rw [← S.bV.sum_repr x]
    rw [map_sum]
    simp only [map_smulₛₗ, bW_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem coef_injective : Function.Injective P.coef := by
  intro x x' h
  apply S.bV.repr.injective
  ext j
  apply σ.injective
  rw [← repr_coef P, ← repr_coef P, h]

theorem extL_injective : Function.Injective P.extL := by
  intro f f' h
  apply Subtype.ext
  funext c
  apply coef_injective P
  rw [← ext_y, ← ext_y]
  exact congrFun h _

theorem eq_of_reps {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ)
    (h : ∀ c, F (P.y c) = F' (P.y c)) : F = F' := by
  funext g
  obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
  rw [hF γ _ k, hF' γ _ k, h]

theorem ext_li : LinearIndependent ℂ (fun i => P.extL (S.basis i)) := by
  letI : Algebra K ℂ := σ.toAlgebra
  let Φ : S.Forms →ₗ[K] (S.Cl × S.ιV → K) :=
    { toFun := fun f p => S.bV.repr ((f : S.Cl → S.V) p.1) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro f f' h
    apply Subtype.ext
    funext c
    apply S.bV.repr.injective
    ext j
    exact congrFun h (c, j)
  have h1 := S.basis.linearIndependent.map' Φ hΦ
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  let Ψ : (G → W) →ₗ[ℂ] (S.Cl × S.ιV → ℂ) :=
    { toFun := fun F p => (bW P).repr (F (P.y p.1)) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  refine LinearIndependent.of_comp Ψ ?_
  have e : (⇑Ψ ∘ fun i => P.extL (S.basis i)) = fun i => ⇑(algebraMap K ℂ) ∘ (⇑Φ ∘ ⇑S.basis) i := by
    funext i p
    show (bW P).repr (P.ext _ (P.y p.1)) p.2 = σ (S.bV.repr ((S.basis i : S.Cl → S.V) p.1) p.2)
    rw [ext_y, repr_coef]
  rw [e]
  exact h2

open Classical in

def avgForm (S : CSD K) (c : S.Cl) (x : S.V) : S.Forms :=
  ⟨Pi.single c (∑ g : S.Gam c, S.ρ c g x), by
    intro c' γ
    by_cases h : c' = c
    · subst h
      simp only [Pi.single_eq_same, map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft γ) _ _ fun _ => rfl
    · simp [Pi.single_eq_of_ne h]⟩

theorem ext_span : Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact extMem P f
  · intro F hF
    have hmem : ∀ M : Submodule ℂ (G → W), (∀ f, P.extL f ∈ M) →
        (∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j))) ∈ M := fun M hM =>
      M.sum_mem fun c _ => M.sum_mem fun j _ => M.smul_mem _ (hM _)
    have key : F = ∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j)) := by
      refine eq_of_reps P hF (hmem _ (extMem P)) fun c => ?_
      simp only [Finset.sum_apply, Pi.smul_apply, ClassPres.extL_apply, ext_y]
      rw [Finset.sum_eq_single c]
      · have hg : ∀ g : S.Gam c, ∑ j, (bW P).repr (F (P.y c)) j • P.coef (S.ρ c g (S.bV j)) = F (P.y c) := by
          intro g
          have h1 := hF (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
          rw [stabK_spec] at h1
          conv_rhs => rw [h1, ← (bW P).sum_repr (F (P.y c))]
          simp only [P.coef_act, map_sum, map_smul, Finset.smul_sum, bW_apply]
          exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
        simp only [avgForm, Pi.single_eq_same, map_sum, mul_smul, ← Finset.smul_sum]
        simp only [Finset.smul_sum (s := (Finset.univ : Finset (S.Gam c)))]
        rw [Finset.sum_comm]
        simp only [hg, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
        exact_mod_cast Fintype.card_ne_zero
      · intro c' _ hc
        simp [avgForm, Pi.single_eq_of_ne (Ne.symm hc)]
      · simp
    rw [key]
    exact hmem _ fun f => Submodule.subset_span ⟨f, rfl⟩

end GlobalTheory.PresBasic

namespace GlobalTheory

theorem classPres_basic : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.Isom ∧ P.ExtBij ∧ (∀ (f : S.Forms) c, P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c)) ∧ Function.Injective P.extL :=
  fun _ _ _ _ _ _ P => ⟨PresBasic.extMem P, PresBasic.isom P, ⟨PresBasic.ext_li P, PresBasic.ext_span P⟩,
    PresBasic.ext_y P, PresBasic.extL_injective P⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineHodgeTateMultiplicityNeZeroOfJumpStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL), Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  first | exact @GlobalTheory.HTW.Rec.jump_multV_ne_zero | exact GlobalTheory.HTW.Rec.jump_multV_ne_zero | (intros; apply GlobalTheory.HTW.Rec.jump_multV_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.DoubleCosetComm

variable {G : Type} [Group G]

def InDC (J : Subgroup G) (x g : G) : Prop := ∃ k₁ k₂ : J, g = (k₁ : G) * x * k₂

theorem InDC.mul {J : Subgroup G} {x g a b : G} (h : InDC J x g) (ha : a ∈ J) (hb : b ∈ J) :
    InDC J x (a * g * b) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨⟨a, ha⟩ * u, v * ⟨b, hb⟩, by simp [mul_assoc]⟩

theorem InDC.inv {J : Subgroup G} {x g : G} (h : InDC J x g) : InDC J x⁻¹ g⁻¹ := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨v⁻¹, u⁻¹, by simp [mul_assoc]⟩

open Classical in

theorem card_filter_le {J : Subgroup G} {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B)
    (P Q : G → Prop) (ψ : G → G) (h1 : ∀ a ∈ A, P a → InDC J y (ψ a))
    (h2 : ∀ a ∈ A, P a → ∀ k ∈ J, Q (ψ a * k))
    (h3 : ∀ a ∈ A, ∀ a' ∈ A, (ψ a)⁻¹ * ψ a' ∈ J → a⁻¹ * a' ∈ J) :
    (A.filter P).card ≤ (B.filter Q).card := by
  have hex : ∀ a : G, ∃ b : G, a ∈ A → P a → b ∈ B ∧ b⁻¹ * ψ a ∈ J := by
    intro a
    by_cases h : a ∈ A ∧ P a
    · obtain ⟨b, hb, -⟩ := hB.2 _ (h1 a h.1 h.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨1, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose r hr using hex
  refine Finset.card_le_card_of_injOn r ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hb, hj⟩ := hr a ha.1 ha.2
    refine ⟨hb, ?_⟩
    have := h2 a ha.1 ha.2 _ (J.inv_mem hj)
    simpa [mul_assoc] using this
  · intro a ha a' ha' e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ha'
    have hj := (hr a ha.1 ha.2).2
    have hj' := (hr a' ha'.1 ha'.2).2
    rw [← e] at hj'
    have h4 : (ψ a)⁻¹ * ψ a' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hj) hj'
    exact (hA.2 a' (hA.1 a' ha'.1)).unique ⟨ha.1, h3 a ha.1 a' ha'.1 h4⟩ ⟨ha'.1, by simp⟩

section Theta

variable {J L : Subgroup G} {θ : G → G}
  (hm : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (hi : ∀ x ∈ L, θ (θ x) = x)
  (hK : ∀ k ∈ J ⊓ L, θ k ∈ J) (hL : ∀ g ∈ L, θ g ∈ L)
  (hdc : ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)

include hm in
theorem theta_inv {g : G} (hg : g ∈ L) : θ g⁻¹ = (θ g)⁻¹ := by
  have h1 : θ 1 = 1 := by
    have h := hm 1 L.one_mem 1 L.one_mem
    rw [mul_one] at h
    have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h'
  apply eq_inv_of_mul_eq_one_left
  rw [← hm _ hg _ (L.inv_mem hg), mul_inv_cancel, h1]

include hm hi hK hL in
theorem theta_coset {a a' : G} (ha : a ∈ L) (ha' : a' ∈ L) (h : θ a * (θ a')⁻¹ ∈ J) : a⁻¹ * a' ∈ J := by
  have hl : a'⁻¹ * a ∈ L := L.mul_mem (L.inv_mem ha') ha
  have e : θ (a'⁻¹ * a) = θ a * (θ a')⁻¹ := by
    rw [hm _ (L.inv_mem ha') _ ha, theta_inv hm ha']
  have := hK (θ (a'⁻¹ * a)) ⟨e ▸ h, hL _ hl⟩
  rw [hi _ hl] at this
  simpa using J.inv_mem this

include hdc in
theorem InDC.theta {x g : G} (h : InDC J x g) (hg : g ∈ L) : InDC J x (θ g) := by
  obtain ⟨a, ha, b, hb, e⟩ := hdc g hg
  rw [e]
  exact h.mul ha.1 hb.1

include hm hi hK hL hdc in
theorem card_le_inv {x : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x⁻¹ A') (hAL : ∀ a ∈ A, a ∈ L) :
    A.card ≤ A'.card := by
  classical
  have := card_filter_le hA hA' (fun _ => True) (fun _ => True) (fun a => (θ a)⁻¹)
    (fun a ha _ => (InDC.theta hdc (hA.1 a ha) (hAL a ha)).inv) (fun _ _ _ _ _ => trivial)
    (fun a ha a' ha' h => theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa using h))
  simpa using this

open Classical in
include hm hi hK hL hdc in
theorem card_conv_le {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    {z : G} (hz : z ∈ L) :
    (A.filter fun a => InDC J y (a⁻¹ * z)).card ≤ (B.filter fun b => InDC J x (b⁻¹ * z)).card := by
  obtain ⟨k, hk, k', hk', e⟩ := hdc z hz
  refine card_filter_le hA hB _ _ (fun a => z * k' * (θ a)⁻¹) ?_ ?_ ?_
  · intro a ha hP
    have hl := L.inv_mem (hAL a ha)
    have h1 := InDC.theta hdc hP (L.mul_mem hl hz)
    rw [hm _ hl _ hz, theta_inv hm (hAL a ha), e] at h1
    simpa [mul_assoc] using h1.mul (J.inv_mem hk.1) J.one_mem
  · intro a ha _ c hc
    have h1 := InDC.theta hdc (hA.1 a ha) (hAL a ha)
    simpa [mul_assoc] using h1.mul (J.inv_mem hc) (J.inv_mem hk'.1)
  · intro a ha a' ha' h
    exact theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa [mul_assoc] using h)

end Theta

open Classical in

theorem card_pairs {J L : Subgroup G} {y : G} {A B : Finset G} (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    (hBL : ∀ b ∈ B, b ∈ L) {z : G} (hz : z ∈ L) :
    ((A ×ˢ B).filter fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))).card =
      (A.filter fun a => InDC J y (a⁻¹ * z)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have h1 : InDC J y b := hB.1 b hp.1.2
    simpa [mul_assoc] using h1.mul J.one_mem (J.inv_mem hp.2.1)
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' e
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp hp' e
    subst e
    have h4 : b⁻¹ * b' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hp.2.1) hp'.2.1
    have := (hB.2 b' (hB.1 b' hp'.1.2)).unique ⟨hp.1.2, h4⟩ ⟨hp'.1.2, by simp⟩
    rw [this]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨b, ⟨hb, hj⟩, -⟩ := hB.2 _ ha.2
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨ha.1, hb⟩, ?_, L.mul_mem (L.inv_mem hz) (L.mul_mem (hAL a ha.1) (hBL b hb))⟩
    simpa [mul_assoc] using J.inv_mem hj

theorem dcOp_comm_and_card : ∀ {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J L : Subgroup G) (χ : J →* ℂˣ) (x y : G) (A B A' : Finset G) (F : G → W), (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ B, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J y B → IsDC J x⁻¹ A' → (∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) → dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  classical
  intro G W _ _ _ J L χ x y A B A' F _ hχ ⟨θ, hL, hm, hi, hK, hdc⟩ hAL hBL hAL' hA hB hA' hF
  refine ⟨?_, le_antisymm (card_le_inv hm hi hK hL hdc hA hA' hAL)
    (card_le_inv hm hi hK hL hdc hA' (by rwa [inv_inv]) hAL')⟩
  have hFK : ∀ g g' : G, (g : G ⧸ (J ⊓ L)) = g' → ∀ h, F (h * g) = F (h * g') := by
    intro g g' e h
    rw [QuotientGroup.eq] at e
    have := hF ⟨_, e.1⟩ (h * g)
    rw [hχ ⟨_, e.1⟩ e.2] at this
    simpa [mul_assoc] using this.symm
  have hms : (A ×ˢ B).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) =
      (B ×ˢ A).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hz : z ∈ L
      · have e1 := card_pairs (A := A) hB hAL hBL hz
        have e2 := card_pairs (A := B) hA hBL hAL hz
        have e3 := le_antisymm (card_conv_le hm hi hK hL hdc hA hB hAL hz)
          (card_conv_le hm hi hK hL hdc hB hA hBL hz)
        have := e1.trans (e3.trans e2.symm)
        rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val] at this
        convert this
      · have hz' : ∀ C D : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ D, a ∈ L) →
            Multiset.filter (fun p : G × G => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) (C ×ˢ D).val = 0 := by
          intro C D hC hD
          rw [Multiset.filter_eq_nil]
          intro p hp e
          rw [Finset.mem_val, Finset.mem_product] at hp
          rw [QuotientGroup.eq] at e
          apply hz
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (hC _ hp.1) (hD _ hp.2)) (L.inv_mem e.2)
        rw [hz' A B hAL hBL, hz' B A hBL hAL]
  funext h
  have key : ∀ C D : Finset G, dcOp C (dcOp D F) h =
      (((C ×ˢ D).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L)))).map fun q => F (h * q.out)).sum := by
    intro C D
    rw [Multiset.map_map]
    change _ = ∑ p ∈ C ×ˢ D, _
    rw [Finset.sum_product]
    simp only [dcOp, Function.comp]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
    exact hFK _ _ (QuotientGroup.out_eq' _).symm h
  rw [key, key, hms]

end GlobalTheory.DoubleCosetComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLiftStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_frobenius_lift : ∀ (E : Type) [Field E] [NumberField E] (p n : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → φ ^ n = 1 → ∃ (W Qq : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field Qq) (_ : Algebra W Qq) (i : E →+* Qq) (σ : Qq ≃+* Qq), IsFractionRing W Qq ∧ Irreducible (p : W) ∧ Nat.card (W ⧸ Ideal.span {(p : W)}) = Nat.card (𝓞 E ⧸ Q.asIdeal) ∧ IsAdicComplete (Ideal.span {(p : W)}) W ∧ (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) ∧ σ ^ n = 1 ∧ (∀ x : E, σ (i x) = i (φ x)) ∧ (∀ x : E, Formalism.L2.Col.IntAt Q x ↔ i x ∈ Set.range (algebraMap W Qq)) ∧ ∀ (y : W) (k : ℕ), ∃ (x : 𝓞 E) (z : W), i (x : E) = algebraMap W Qq (y + (p : W) ^ k * z) := by
  first | exact @GlobalTheory.UnramCompletion.exists_completion_frobenius | exact GlobalTheory.UnramCompletion.exists_completion_frobenius | (intros; apply GlobalTheory.UnramCompletion.exists_completion_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprimeStatement
section
open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime : ∀ (G : GDatum) (N : ℕ), 0 < N → ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  first | (exact @GlobalTheory.GoodPrime.exists_datum) | (exact GlobalTheory.GoodPrime.exists_datum) | (intros; apply GlobalTheory.GoodPrime.exists_datum  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodOrdinaryModelAtTwoCmLatticeSevenModEight
section
namespace GlobalTheory.ThLoc

theorem goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight : Formalism.L2.Th1.Top.GoodModelTwo :=
  GlobalTheory.ThLoc.GoodTwo.goodModelTwo

end GlobalTheory.ThLoc
end

