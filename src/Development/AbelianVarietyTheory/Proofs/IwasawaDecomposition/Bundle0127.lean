import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix Filter

namespace GlobalTheory.CuspRep.LocSph

theorem exists_fixed_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (φ : V) (h0 : φ ≠ 0) (hK : ∀ k ∈ K, ρ k φ = φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add] at h5
          have h6 : f i (σ k v - v) = x - ρ k x := by
            rw [map_sub, hf]; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem hx (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add, ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem tendsto_sLoc (y : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E)
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : Tendsto (fun v => sLoc E v (y v)) cofinite (𝓝 0) := by
  classical
  have h := (GlobalTheory.Mem.UnrAe.tendsto_finSingle y hy).sub
    (GlobalTheory.Mem.UnrAe.tendsto_finSingle (L := E) (fun _ => 0) fun _ => by simp)
  rw [sub_self] at h
  refine h.congr fun w => ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  change Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w (y w) v -
      Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w 0 v =
      (Pi.single w (y w) : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

theorem tendsto_corner (y : ∀ v : HeightOneSpectrum (𝓞 E), Matrix (Fin a) (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => corner (matN a (sLoc E v)) ((y v).map (v.adicCompletionIntegers E).subtype)) cofinite (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((tendsto_const_nhds (x := (1 : Matrix (Fin a) (Fin a) (Af E)) i j)).sub
    (tendsto_sLoc (E := E) (fun v => (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) fun v => by
      rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _])).add
    (tendsto_sLoc (fun v => (y v i j : v.adicCompletion E)) fun v => (y v i j).2)
  rw [sub_zero, add_zero] at h
  exact h

theorem tendsto_locGL (y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => locGL E a v (GeneralLinearGroup.map (v.adicCompletionIntegers E).subtype (y v))) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (tendsto_corner fun v => (y v).val).prodMk_nhds
    ((MulOpposite.continuous_op.tendsto _).comp (tendsto_corner fun v => ((y v)⁻¹).val))

theorem eventually_mem {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 1) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := by
  have h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype y) ∈ U →
      ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
        locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := fun w => by
    by_contra hc
    push Not at hc
    obtain ⟨-, g, hg⟩ := hc 1
    exact hg (hc g).1
  choose y hy using h
  exact ((tendsto_locGL y).eventually_mem hU).mono fun w hw => hy w hw

variable [IsTotallyComplex E]

def Maps (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ π.V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : π.IsLocComp w σ) : ⨆ f : Maps π w σ, LinearMap.range f.1 = π.V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps π w σ) v, act o (f.1 v) ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => π.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps π w σ) ⟨v, rfl⟩
  refine (π.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps π w σ, LinearMap.range f.1) ≤ (⨆ f : Maps π w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hf⟩ := h
    refine h0 (LinearMap.ext fun v => Subtype.ext ?_)
    have : (f v).1 ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨π.V.subtype ∘ₗ f, fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩ :
        Maps π w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem locComp_spherical : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → ∃ v : σ.V, v ≠ 0 ∧ ∀ g : GL (Fin a) (w.adicCompletionIntegers E), σ.ρ (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) v = v := by
  intro E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨v, h1, h2⟩ := exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
    (fun f : Maps π w σ => f.1) (fun f => f.2.2)
    (Set.range (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype)) φ h0
    (by rintro _ ⟨g, rfl⟩; exact hw g) (by rw [iSup_range_eq π w σ hσ]; exact hφ)
  exact ⟨v, h1, fun g => h2 _ ⟨g, rfl⟩⟩

end GlobalTheory.CuspRep.LocSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatBoundPre
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_nat_bound_pre {ι : Type} [Finite ι] (s : ι → ℝ) (c : ℕ) :
    ∃ a : ℕ, c < 4 * a ∧ ∀ i, s i ≤ 2 * (a : ℝ) := by
  obtain ⟨b, hb⟩ := (Set.finite_range s).bddAbove
  obtain ⟨a, ha⟩ := exists_nat_ge b
  refine ⟨a + c + 1, by omega, fun i => ?_⟩
  have h1 : s i ≤ b := hb ⟨i, rfl⟩
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  linarith

theorem exists_pre_two_words : ∃ B : Pre, Nonempty (PreX B) ∧ 2 ≤ Fintype.card B.Word ∧ B.host.TT.Nonempty ∧ (letI := B.host.cmStar; DiagSpaces B.sp ∧ ∀ j, B.sp.Vneg j = false) ∧ (∃ (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧ (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧ ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) := by
  obtain ⟨R, hRi, hRo, hR⟩ : ∃ R : Ranks, Function.Injective R.h ∧ R.o ^ 64 ≤ 2 ^ R.e ∧ 2 ≤ R.e := by
    refine ⟨Formalism.MainNotions.Inhab.Rt 0, Formalism.HC.frameCyc_h_injective 2 1, ?_, le_rfl⟩
    have h1 : (Formalism.MainNotions.Inhab.Rt 0).o = 1 := Formalism.HC.cyclicFrame_index 2
    rw [h1, one_pow]
    exact Nat.one_le_two_pow
  obtain ⟨H, -, -, -, hcc, hTT, -, hBB, hlev, hg, hπ, hp, hp'⟩ :=
    GlobalTheory.T.exists_host_congruence_primes R hRi hRo hR 0 (2 * R.f * R.k + 1) {0}
  have hk : 0 < R.k - 2 := by have := R.m_add_three_le_k; omega
  let c : Fin 2 → Fin (R.k - 2) → Bool := fun u _ => decide (u = 0)
  have hc : Function.Injective c := by
    intro u u' h
    have h0 := congrFun h ⟨0, hk⟩
    simp only [c, decide_eq_decide] at h0
    fin_cases u <;> fin_cases u' <;> simp_all
  obtain ⟨hcW, hW, P, hPR, hPH, hPW, hPc⟩ :=
    GlobalTheory.T.exists_harish_chandra_weights R H H.u0 hcc hlev hBB 2 (by norm_num) c 1 (R.t + 3)
      (fun _ => ((R.k - 2 : ℕ) : ℤ) * (4 * (1 : ℕ))) (fun _ => -1) (fun _ => 1) le_rfl (by omega)
      (fun _ => ⟨le_rfl, le_rfl, le_rfl⟩)
  obtain ⟨R', H', hcc', hlev', hBB', Wd, u₀, hcW', hv, hb, he, hf, hl⟩ := P
  dsimp only at hPR hPH hPW hPc
  subst hPR hPW
  have e1 : H' = H := eq_of_heq hPH
  have e2 : hcW' = hcW := eq_of_heq hPc
  subst e1 e2
  rename_i inst
  obtain ⟨a, ha1, ha2⟩ := exists_nat_bound_pre
    (fun x : Fin 2 × Fin (R'.m + 1) × Tau R' => ((Formalism.BasicNotions.Examples₂.lamOf (hcW' x.1 x.2.2) x.2.1.1).spread : ℝ))
    (2 * R'.f * R'.N R'.m + 1)
  let P : PreCh := @PreCh.mk R' H' hcc' hlev' hBB' (Fin 2) inst u₀ hcW' hv hb he hf hl
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_level_characters_large P (4 * a)
  obtain ⟨sp, hT, hY, hA, hV, hz, hD, -⟩ := GlobalTheory.Mem.exists_diagSpaces_ofCh P L
  choose πg hπ1 hπ2 hπ3 using hπ
  have hne : Nonempty (Tau R') := Fintype.card_pos_iff.1 (by
    rw [card_Tau H']; unfold Ranks.f Ranks.n; have := R'.ord_pos; positivity)
  refine ⟨Pre.ofCh P L sp hT hY hA hV hz, ⟨{
      piG := πg
      piG_K := hπ1
      piG_norm := hπ2
      piG_cong := hπ3
      piT := L.piT
      piT_K := L.piT_K
      piT_norm := L.piT_norm
      piT_cong := fun u => Ideal.mem_span_singleton.1 (L.piT_cong u)
      pde_split := ⟨?_, ?_⟩
      ccK_top := hcc'
      e_even := ?_
      hcW_inj := ?_
      a := a
      g_big := ?_
      T_gt := ?_
      a_gt := ?_
      spread_le := ?_ }⟩, ?_, ?_, hD, 1, c, one_pos, hc, ?_, ?_⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver H'.E H'.pde_prime).symm.trans
      (GlobalTheory.HostSplit.split_of_one_mod R' H' _ H'.pde_prime hp).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver H'.E H'.pde'_prime).symm.trans
      (GlobalTheory.HostSplit.split_of_one_mod R' H' _ H'.pde'_prime hp').1
  · intro j
    refine UpperTheory.Mu.muq_of_const H' (Equiv.refl _)
      (1 + (j.1 : ℤ) * (2 * ((R'.t + 3 : ℕ) : ℤ)) + ((R'.t + 3 : ℕ) : ℤ)) (fun τ => ?_)
    show (hcW' u₀ τ).e j = _
    rw [((hW u₀ τ).2.1 j).2, ((hW u₀ τ).2.1 j).1]
    push_cast
    ring
  · show Function.Injective hcW'
    intro u u' h
    obtain ⟨τ⟩ := hne
    have h1 := (hW u τ).2.2.2 0 hk
    have h2 := (hW u' τ).2.2.2 0 hk
    rw [h, h2] at h1
    have h3 : (if c u' ⟨0, hk⟩ = true then ((1 : ℕ) : ℚ) else 0) = if c u ⟨0, hk⟩ = true then ((1 : ℕ) : ℚ) else 0 :=
      sub_right_injective h1
    clear h h1 h2
    revert h3
    simp only [c]
    revert u u'
    simp [Fin.forall_fin_two]
  · intro i
    have := hg i
    show 2 * R'.f * R'.k < H'.g i - 1
    omega
  · intro u
    have := hL u
    show 4 * (a : ℝ) < (L.T u : ℝ)
    exact_mod_cast this
  · show ((2 * R'.f * R'.N R'.m + 1 : ℕ) : ℝ) < 4 * (a : ℝ)
    exact_mod_cast ha1
  · intro u j hj τ
    exact ha2 (u, ⟨j, Nat.lt_succ_of_le hj⟩, τ)
  · show 2 ≤ @Fintype.card (Fin 2) inst
    rw [Subsingleton.elim inst (Fin.fintype 2), Fintype.card_fin]
  · show H'.TT.Nonempty
    rw [hTT]
    exact Finset.singleton_nonempty _
  · intro w τ l h
    have h' : l + 1 < R'.k - 1 := h
    show (hcW' w τ).v ⟨l, by omega⟩ - (hcW' w τ).v ⟨l + 1, h'⟩ = 4 * 1
    rw [(hW w τ).1, (hW w τ).1]
    have h3 : R'.k - 2 - l = (R'.k - 2 - (l + 1)) + 1 := by omega
    dsimp only
    rw [h3]
    push_cast
    ring
  · intro w τ l h
    have h1 := (hW w τ).2.2.2 l h
    rw [Nat.cast_one] at h1
    exact h1

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemOfIsLattice
section
namespace GlobalTheory.SmulMemOfIsLattice

theorem exists_smul_mem_of_isLattice {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (B : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n))
    (hB : Submodule.IsLattice E B) (x : Formalism.L2.Col.Sp E n) :
    ∃ r ∈ nonZeroDivisors (NumberField.RingOfIntegers E), r • x ∈ B := by
  have hx : x ∈ Submodule.span E (B : Set (Formalism.L2.Col.Sp E n)) := by
    rw [hB.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_mem hr hs, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ hry
    · rw [mul_smul]; exact B.smul_mem _ hsz
  | smul c y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    refine ⟨r * b, mul_mem hr hb, ?_⟩
    have hb0 : algebraMap (NumberField.RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h : (r * b) • ((algebraMap (NumberField.RingOfIntegers E) E a / algebraMap (NumberField.RingOfIntegers E) E b) • y) = a • (r • y) := by
      rw [← algebraMap_smul E (r * b), ← algebraMap_smul E a, ← algebraMap_smul E r y, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h]
    exact B.smul_mem _ hry

end GlobalTheory.SmulMemOfIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolEmb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infEmb_exists (τ : E →+* ℂ) (w : InfinitePlace F) (hw : w.embedding = τ.comp (algebraMap F E)) :
    ∃ θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  let _ : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : Ainf F →ₐ[F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x =>
        (InfinitePlace.Completion.extensionEmbedding_coe w _).trans (DFunLike.congr_fun hw x) }
  let g : E →ₐ[F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[F] (1 : E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem infEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ)
    (h' : IsInfEmb τ θ') : θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem existsUnique_infEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : E →+* ℂ, ∃! θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  intro F E _ _ _ _ _ σ h τ
  have := h.1
  have hr : (InfinitePlace.mk (τ.comp (algebraMap F E))).IsReal := IsTotallyReal.isReal _
  have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)
  obtain ⟨θ, hθ⟩ := infEmb_exists τ _ hw
  exact ⟨θ, hθ, fun θ' h' => infEmb_unique τ θ' θ h' hθ⟩

end GlobalTheory.Mem.VolEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
section
noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

def FinAlg (T : Set ℂ) : Prop :=
  ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧ T ⊆ (Subfield.closure (Z : Set ℂ) : Set ℂ)

theorem FinAlg.mono {T T' : Set ℂ} (h : FinAlg T') (hT : T ⊆ T') : FinAlg T := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, hT.trans hsub⟩

theorem finAlg_of_finite {T : Set ℂ} (h : T.Finite) (ha : ∀ z ∈ T, IsAlgebraic ℚ z) : FinAlg T := by
  refine ⟨h.toFinset, fun z hz => ha z (h.mem_toFinset.mp hz), ?_⟩
  rw [h.coe_toFinset]
  exact Subfield.subset_closure

theorem finAlg_biUnion {κ : Type} {s : Set κ} (hs : s.Finite) {T : κ → Set ℂ} (h : ∀ k ∈ s, FinAlg (T k)) :
    FinAlg (⋃ k ∈ s, T k) := by
  classical
  choose! Z hZ hsub using h
  refine ⟨hs.toFinset.biUnion Z, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact hZ k (hs.mem_toFinset.mp hk) z hzk
  · refine Set.iUnion₂_subset fun k hk => (hsub k hk).trans (Subfield.closure_mono ?_)
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨k, hs.mem_toFinset.mpr hk, hz⟩

theorem FinAlg.union {T T' : Set ℂ} (h : FinAlg T) (h' : FinAlg T') : FinAlg (T ∪ T') := by
  classical
  obtain ⟨Z, hZ, hsub⟩ := h
  obtain ⟨Z', hZ', hsub'⟩ := h'
  refine ⟨Z ∪ Z', fun z hz => ?_, Set.union_subset ?_ ?_⟩
  · rcases Finset.mem_union.mp hz with hz | hz
    · exact hZ z hz
    · exact hZ' z hz
  · exact hsub.trans (Subfield.closure_mono (by simp))
  · exact hsub'.trans (Subfield.closure_mono (by simp))

theorem FinAlg.closure {T : Set ℂ} (h : FinAlg T) : FinAlg (Subfield.closure T : Set ℂ) := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, SetLike.coe_subset_coe.mpr (Subfield.closure_le.mpr hsub)⟩

variable {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ)

def jetSet (n : ℕ) : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b)
    (e : DVar X.Tau a b →₀ ℕ), InRange S M c N N' x ∧ e.degree = n ∧
      z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) e}

def JetAlg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange S M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      IsAlgebraic ℚ ((A.chiF a b N N')⁻¹ * derivAt0 (A.thInd S N N' c x) e)

def VacEq : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

end GlobalTheory.Mem.Col2.JetEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExistsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_etaTilde_character_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  first | exact @GlobalTheory.Mem.EtaT.etaT_exists | exact GlobalTheory.Mem.EtaT.etaT_exists | (intros; apply GlobalTheory.Mem.EtaT.etaT_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem isCMFam_host (R : Ranks) (H : Host R) (I : Type) (e : I ≃ R.Psi) :
    IsCMFam (fun i => H.emb (e i).1) := by
  refine ⟨fun i j h => ?_, fun w => ?_⟩
  · rcases NumberField.InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact e.injective (GlobalTheory.CuspAlgComparison.tau_injective H h1)
    · exact absurd h1.symm (GlobalTheory.CuspAlgComparison.tau_ne_conj H (e j) (e i))
  · obtain ⟨τ, h | h⟩ := GlobalTheory.CuspAlgComparison.emb_cases H w.embedding
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      rfl
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      exact (NumberField.InfinitePlace.mk_conjugate_eq _).symm

end GlobalTheory.Mem.Vol
end

