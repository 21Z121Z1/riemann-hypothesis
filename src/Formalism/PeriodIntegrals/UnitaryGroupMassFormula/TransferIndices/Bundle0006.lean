import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.Bundle0005

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.BlockMain
section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Side

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ} {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V}
  {Γ : Matrix (Fin n) (Fin n) K}

theorem BlockHyp.side (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (H : BlockHyp X Y Φ Ψ Γ)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hLsp : Submodule.span K (L : Set V) = ⊤)
    (hΦL : ∀ i, ∀ x ∈ L, x ∈ X → Φ i x ∈ L) (hΨL : ∀ j, ∀ y ∈ L, y ∈ Y → Ψ j y ∈ L) :
    (latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K)) ≤
        L ⊓ Y.restrictScalars (𝓞 K) ∧
      Submodule.span K (((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map
        ((Φt Φ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = Y ∧
      0 ≤ idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ∧
      idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ≤
        (Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) : ℤ) * vAdd w Γ.det := by
  set LX := L ⊓ X.restrictScalars (𝓞 K) with hLXd
  set LY := L ⊓ Y.restrictScalars (𝓞 K) with hLYd
  have hLX : Submodule.span K (LX : Set V) = X := cut_span L hLsp X
  have hLY : Submodule.span K (LY : Set V) = Y := cut_span L hLsp Y
  have fgLX : LX.FG := fg_cut L hL X
  have fgLY : LY.FG := fg_cut L hL Y
  set LP := latPow (Fin n) LX with hLPd
  have fgLP : LP.FG := Submodule.fg_pi fun _ => fgLX
  have hLPsp : Submodule.span K (LP : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hLPd, span_latPow, hLX]
  have hLPX : ∀ x ∈ LP, x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  set A := LP.map ((Φt Φ).restrictScalars (𝓞 K)) with hAd
  have fgA : A.FG := fgLP.map _
  have hAle : A ≤ LY := by
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, H.phi_mem x (hLPX x hx)⟩
    simp only [LinearMap.coe_restrictScalars, Φt_apply]
    exact L.sum_mem fun i _ => hΦL i (x i) (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).1
      (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have hAsp : Submodule.span K (A : Set V) = Y := by
    rw [hAd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLPsp, H.map_phi]
  refine ⟨hAle, hAsp, idx_nonneg_of_le hI w LY A fgLY fgA (hLY.trans hAsp.symm) hAle, ?_⟩

  set Bt := LY.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) with hBtd
  have fgBt : Bt.FG := fgLY.map _
  have hBle : Bt ≤ LP := by
    rintro _ ⟨y, hy, rfl⟩ j _
    have hy' := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨hΨL j y hy'.1 hy'.2, H.h3 j y hy'.2⟩
  have hBsp : Submodule.span K (Bt : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hBtd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLY, H.map_psi]
  have hΨA : A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) = LP.map ((matV Γ).restrictScalars (𝓞 K)) := by
    rw [hAd, ← Submodule.map_comp]
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (H.psiPhi x (hLPX x hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, H.psiPhi x (hLPX x hx)⟩
  have hmat := idx_matV hI w LX fgLX Γ H.det
  rw [← hLPd, ← hΨA] at hmat
  have hΨAsp : Submodule.span K ((A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → V)) :
      Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hΨA]; exact span_map_matV Γ H.det LP X hLPsp
  have hch := idx_chain hI w LP Bt (A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K))) fgLP fgBt (fgA.map _)
    (by rw [hLPsp, hBsp]) (by rw [hΨAsp, hBsp])
  have hinj := idx_map_inj hI w (LinearMap.pi Ψ) LY A fgLY fgA (hLY.trans hAsp.symm)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp hy).2 h0)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp (hAle hy)).2 h0)
  have hnn := idx_nonneg_of_le hI w LP Bt fgLP fgBt (by rw [hLPsp, hBsp]) hBle
  rw [← hBtd] at hinj
  rw [hmat, ← hinj] at hch
  linarith

end Side

theorem block_index_formula (hI : IdxCalc) : BlockIdx := by
  intro K _ _ V _ _ _ _ n X Y Φ Ψ Γ hdet h1 h2 h3 h4 M N hMfg hNfg hMsp hNsp hΦM hΨM hΦN hΨN
  haveI : FiniteDimensional K V := by
    obtain ⟨s, hs⟩ := hMfg
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [← hMsp, ← hs, Submodule.span_span_of_tower]
  set Γk : Matrix (Fin n) (Fin n) K := Γ.map (algebraMap (𝓞 K) K) with hΓk
  have hdetk : Γk.det = algebraMap (𝓞 K) K Γ.det := (RingHom.map_det _ _).symm
  have H : BlockHyp X Y Φ Ψ Γk :=
    ⟨by rw [hdetk]; exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hdet,
      fun i j x hx => by rw [h1 i j x hx]; rfl, h2, h3, h4⟩
  have hrX : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ →
      Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := fun L hL => rk_cut L hL X
  refine ⟨by rw [rk_cut M hMsp Y, rk_cut M hMsp X, H.finrank], fun w => ?_⟩
  obtain ⟨hAle, hAsp, hA0, hA1⟩ := H.side hI w M hMfg hMsp hΦM hΨM
  obtain ⟨hBle, hBsp, hB0, hB1⟩ := H.side hI w N hNfg hNsp hΦN hΨN
  rw [hdetk] at hA1 hB1
  rw [hrX N hNsp, ← hrX M hMsp] at hB1
  set MX := M ⊓ X.restrictScalars (𝓞 K)
  set NX := N ⊓ X.restrictScalars (𝓞 K)
  set MY := M ⊓ Y.restrictScalars (𝓞 K)
  set NY := N ⊓ Y.restrictScalars (𝓞 K)
  set A := (latPow (Fin n) MX).map ((Φt Φ).restrictScalars (𝓞 K))
  set B := (latPow (Fin n) NX).map ((Φt Φ).restrictScalars (𝓞 K))
  have fgMX : MX.FG := fg_cut M hMfg X
  have fgNX : NX.FG := fg_cut N hNfg X
  have fgMY : MY.FG := fg_cut M hMfg Y
  have fgNY : NY.FG := fg_cut N hNfg Y
  have fgA : A.FG := (Submodule.fg_pi fun _ => fgMX).map _
  have fgB : B.FG := (Submodule.fg_pi fun _ => fgNX).map _
  have sMY : Submodule.span K (MY : Set V) = Y := cut_span M hMsp Y
  have sNY : Submodule.span K (NY : Set V) = Y := cut_span N hNsp Y
  have c1 := idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans hAsp.symm) (sNY.trans hAsp.symm)
  have c2 := idx_chain hI w A B NY fgA fgB fgNY (hAsp.trans hBsp.symm) (sNY.trans hBsp.symm)
  have hLX : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K)),
      x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun L x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have c3 := idx_map_inj hI w (Φt Φ) (latPow (Fin n) MX) (latPow (Fin n) NX)
    (Submodule.fg_pi fun _ => fgMX) (Submodule.fg_pi fun _ => fgNX)
    (by rw [span_latPow, span_latPow, cut_span M hMsp X, cut_span N hNsp X])
    (fun x hx h0 => H.phi_inj x (hLX M x hx) h0) (fun x hx h0 => H.phi_inj x (hLX N x hx) h0)
  have c4 := idx_pi hI w (fun _ : Fin n => MX) (fun _ : Fin n => NX) (fun _ => fgMX) (fun _ => fgNX)
    (fun _ => by rw [cut_span M hMsp X, cut_span N hNsp X])
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at c4
  have c5 : idxAt w B NY = -idxAt w NY B := idx_anti w B NY
  have key : idxAt w MY NY = idxAt w MY A + (n : ℤ) * idxAt w MX NX - idxAt w NY B := by
    rw [c1, c2, c5, ← c3]
    have : idxAt w (latPow (Fin n) MX) (latPow (Fin n) NX) = (n : ℤ) * idxAt w MX NX := c4
    rw [this]; ring
  have hD1 : -((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det)) ≤
      idxAt w MY NY - (n : ℤ) * idxAt w MX NX := by rw [key]; linarith
  have hD2 : idxAt w MY NY - (n : ℤ) * idxAt w MX NX ≤
      (Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) := by rw [key]; linarith
  have hfin : |((idxAt w MY NY - (n : ℤ) * idxAt w MX NX : ℤ) : ℝ)| ≤
      (((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) : ℤ) : ℝ) := by
    rw [abs_le]; constructor
    · exact_mod_cast hD1
    · exact_mod_cast hD2
  push_cast at hfin
  exact hfin

end PI.Dv.TIW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.SumIndexFormula
section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

theorem sum_index_formula (hI : IdxCalc) : SumIdx := by
  intro K _ _ V _ _ _ _ S _ _ π m hm horth M N hMfg hNfg hMsp hNsp hMint hNint
  haveI : FiniteDimensional K V := by
    obtain ⟨s, hs⟩ := hMfg
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [← hMsp, ← hs, Submodule.span_span_of_tower]
  set P : V →ₗ[K] V := ∑ t, π t with hP
  have hcomp : ∀ s t z, π s (π t z) = if s = t then π t z else 0 := by
    intro s t z
    have := congrArg (fun f => f z) (horth s t)
    simp only [LinearMap.comp_apply] at this
    rw [this]; split_ifs with h
    · subst h; rfl
    · rfl
  have hPπ : ∀ s z, P (π s z) = π s z := by
    intro s z
    rw [hP, LinearMap.sum_apply]
    simp only [hcomp]
    rw [Finset.sum_ite_eq' Finset.univ s]; simp
  have hYs : ∀ s, LinearMap.range (π s) ≤ LinearMap.range P := by
    rintro s _ ⟨z, rfl⟩; exact ⟨π s z, hPπ s z⟩
  have hdec : ∀ y ∈ LinearMap.range P, y = ∑ s, π s y := by
    rintro _ ⟨z, rfl⟩
    have : ∀ s, π s (P z) = π s z := by
      intro s
      rw [hP, LinearMap.sum_apply, map_sum]
      simp only [hcomp]
      rw [Finset.sum_ite_eq Finset.univ s]; simp
    simp only [this]
    rw [hP, LinearMap.sum_apply]
  have hfix : ∀ s t y, y ∈ LinearMap.range (π s) → π t y = if t = s then y else 0 := by
    rintro s t _ ⟨z, rfl⟩
    rw [hcomp]

  set σ : (S → V) →ₗ[K] V := ∑ s, LinearMap.proj s with hσd
  have hσ : ∀ x : S → V, σ x = ∑ s, x s := fun x => by simp [hσd, LinearMap.sum_apply]
  set YS : Submodule K (S → V) := Submodule.pi Set.univ fun s => LinearMap.range (π s) with hYS
  have hσinj : ∀ x ∈ YS, σ x = 0 → x = 0 := by
    intro x hx h0
    funext t
    have : π t (σ x) = x t := by
      rw [hσ, map_sum]
      simp only [fun s => hfix s t (x s) (hx s (Set.mem_univ s))]
      rw [Finset.sum_ite_eq Finset.univ t]; simp
    rw [← this, h0, map_zero]; rfl
  have hσmap : YS.map σ = LinearMap.range P := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hσ]
      exact Submodule.sum_mem _ fun s _ => hYs s (hx s (Set.mem_univ s))
    · intro y hy
      refine ⟨fun s => π s y, fun s _ => ⟨y, rfl⟩, ?_⟩
      rw [hσ]; exact (hdec y hy).symm
  have hrk : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ →
      Formalism.HN.rkK (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K)) =
        ∑ s, Formalism.HN.rkK (L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) := by
    intro L hL
    rw [rk_cut L hL]
    simp only [rk_cut L hL]
    let f : (∀ s, LinearMap.range (π s)) →ₗ[K] LinearMap.range P := LinearMap.codRestrict _
      (σ ∘ₗ LinearMap.pi (fun s => (LinearMap.range (π s)).subtype ∘ₗ LinearMap.proj s))
      (fun x => by
        rw [← hσmap]; exact ⟨_, fun s _ => (x s).2, rfl⟩)
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h := congrArg Subtype.val hxy
        simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h
        rw [← sub_eq_zero, ← map_sub] at h
        have := hσinj _ (Submodule.sub_mem _ (fun s _ => (x s).2) (fun s _ => (y s).2)) h
        funext s
        apply Subtype.ext
        have := congrFun this s
        simpa [sub_eq_zero] using this
      · rintro ⟨y, hy⟩
        refine ⟨fun s => ⟨π s y, y, rfl⟩, ?_⟩
        apply Subtype.ext
        simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply]
        rw [hσ]
        exact (hdec y hy).symm
    rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
  refine ⟨hrk M hMsp, fun w => ?_⟩

  have side : ∀ L : Submodule (𝓞 K) V, L.FG → Submodule.span K (L : Set V) = ⊤ →
      (∀ s, ∀ x ∈ L, x ∈ LinearMap.range P → ((m : ℕ) : 𝓞 K) • π s x ∈ L) →
      ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K))).FG ∧
      Submodule.span K (((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = LinearMap.range P ∧
      0 ≤ idxAt w (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K))
        ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K))) ∧
      idxAt w (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K))
        ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K))) ≤
        (Formalism.HN.rkK (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K)) : ℤ) * vAdd w ((m : ℕ) : K) := by
    intro L hL hLsp hLint
    have fgpi : (Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).FG :=
      Submodule.fg_pi fun s => fg_cut L hL _
    have hsp : Submodule.span K (((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = LinearMap.range P := by
      rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, span_pi_eq]
      simp only [cut_span L hLsp]
      exact hσmap
    have hle : (Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
        (σ.restrictScalars (𝓞 K)) ≤ L ⊓ (LinearMap.range P).restrictScalars (𝓞 K) := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars]
      rw [hσ]
      refine Submodule.mem_inf.mpr ⟨L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).1, ?_⟩
      exact Submodule.sum_mem _ fun s _ => hYs s (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).2
    have hfgY := fg_cut L hL (LinearMap.range P)
    have hspY := cut_span L hLsp (LinearMap.range P)
    refine ⟨fgpi.map _, hsp, idx_nonneg_of_le hI w _ _ hfgY (fgpi.map _) (hspY.trans hsp.symm) hle,
      idx_le_nat hI w _ _ hfgY (fgpi.map _) (hspY.trans hsp.symm) m hm hle ?_⟩
    intro x hx
    have hx' := Submodule.mem_inf.mp hx
    refine ⟨fun s => ((m : ℕ) : 𝓞 K) • π s x, fun s _ => Submodule.mem_inf.mpr ⟨hLint s x hx'.1 hx'.2, ?_⟩, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      refine ⟨((m : ℕ) : K) • x, ?_⟩
      show π s (((m : ℕ) : K) • x) = ((m : ℕ) : 𝓞 K) • π s x
      rw [map_smul, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K)]
    · simp only [LinearMap.coe_restrictScalars]
      rw [hσ, ← Finset.smul_sum, ← hdec x hx'.2]
  obtain ⟨fgA, spA, hA0, hA1⟩ := side M hMfg hMsp hMint
  obtain ⟨fgB, spB, hB0, hB1⟩ := side N hNfg hNsp hNint
  rw [rk_cut N hNsp (LinearMap.range P), ← rk_cut M hMsp (LinearMap.range P)] at hB1
  set MY := M ⊓ (LinearMap.range P).restrictScalars (𝓞 K)
  set NY := N ⊓ (LinearMap.range P).restrictScalars (𝓞 K)
  set A := (Submodule.pi Set.univ fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
    (σ.restrictScalars (𝓞 K))
  set B := (Submodule.pi Set.univ fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
    (σ.restrictScalars (𝓞 K))
  have fgMY := fg_cut M hMfg (LinearMap.range P)
  have fgNY := fg_cut N hNfg (LinearMap.range P)
  have sMY := cut_span M hMsp (LinearMap.range P)
  have sNY := cut_span N hNsp (LinearMap.range P)
  have c1 := idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans spA.symm) (sNY.trans spA.symm)
  have c2 := idx_chain hI w A B NY fgA fgB fgNY (spA.trans spB.symm) (sNY.trans spB.symm)
  have hmemYS : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ Submodule.pi Set.univ
      (fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)), x ∈ YS :=
    fun L x hx s _ => (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).2
  have c3 := idx_map_inj hI w σ (Submodule.pi Set.univ fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
    (Submodule.pi Set.univ fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
    (Submodule.fg_pi fun s => fg_cut M hMfg _) (Submodule.fg_pi fun s => fg_cut N hNfg _)
    (by rw [span_pi_eq, span_pi_eq]; simp only [cut_span M hMsp, cut_span N hNsp])
    (fun x hx h0 => hσinj x (hmemYS M x hx) h0) (fun x hx h0 => hσinj x (hmemYS N x hx) h0)
  have c4 := idx_pi hI w (fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
    (fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (fun s => fg_cut M hMfg _)
    (fun s => fg_cut N hNfg _) (fun s => by rw [cut_span M hMsp, cut_span N hNsp])
  have c5 : idxAt w B NY = -idxAt w NY B := idx_anti w B NY
  have key : idxAt w MY NY = idxAt w MY A +
      (∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))) - idxAt w NY B := by
    rw [c1, c2, c5, ← c3, c4]; ring
  have hD1 : -((Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K)) ≤ idxAt w MY NY -
      ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) := by rw [key]; linarith
  have hD2 : idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) ≤ (Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K) := by
    rw [key]; linarith
  have hfin : |((idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) : ℤ) : ℝ)| ≤
      (((Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K) : ℤ) : ℝ) := by
    rw [abs_le]; constructor
    · exact_mod_cast hD1
    · exact_mod_cast hD2
  push_cast at hfin
  exact hfin

end PI.Dv.TIW
end
end

