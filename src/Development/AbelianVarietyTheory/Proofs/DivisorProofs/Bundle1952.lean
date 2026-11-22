import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacUniq

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem schr_schr {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  have key : (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) + ((x + w.1) ⬝ᵥ w'.2 + ⅟(2 : K) * (w'.1 ⬝ᵥ w'.2)) =
      ⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) +
        (x ⬝ᵥ (w + w').2 + ⅟(2 : K) * ((w + w').1 ⬝ᵥ (w + w').2)) := by
    have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2
  show ψ _ * (ψ _ * φ (x + w.1 + w'.1)) = ψ _ * (ψ _ * φ (x + (w + w').1))
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v _
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem phase {V : Type} [AddCommGroup V] [Module ℂ V] {φ ψ S : V} {c χ : ℂ} (hne : φ ≠ 0)
    (h1 : φ = (c * χ) • φ) (h2 : ψ = c • S) : S = χ • ψ := by
  have hcχ : c * χ = 1 := by
    by_contra hne'
    have h4 : (c * χ - 1) • φ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact hne ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne'))
  rw [h2, smul_smul, mul_comm, hcχ, one_smul]

theorem sa_bd_uniq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq g hg hSa hBd
  have hψc : Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 Bs.v₁
  have hSB : ∀ γ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁),
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ ∈ GlobalTheory.WeilM.SB _ :=
    fun γ φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB _ _ hψc _ _ hφ
  have hat : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, At (evFin D.host.F Bs.v₁) γ :=
    (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1
  have hacts : ∀ γ, At (evFin D.host.F Bs.v₁) γ → ∀ φ, Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ
      (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function Bs.v₁ φ₀ h0
  obtain ⟨χ, hχ⟩ : ∃ χ : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E) → ℂ, ∀ γ, χ γ =
      Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
        (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) := ⟨_, fun _ => rfl⟩
  have hφ₀ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ₀ = χ γ • φ₀ := by
    intro γ hγ
    rw [hχ]
    exact acts_unique Bs.v₁ hr hx₀ _ _ _ (hacts γ (hat γ hγ) φ₀) (hfix γ hγ)
  have hχ1 : ∀ u, At (evFin D.host.F Bs.v₁) u →
      (u.map (piW Bs.τ₁) = 0 ∨ u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) → χ u = 1 := by
    intro u hu h
    rw [hχ, GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hu h, mul_zero, AddChar.map_zero_eq_one]
  obtain ⟨ψ₀, hψ₀, hιψ₀⟩ := hι.bij.surjOn hg
  have hA : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, γ.map (piW Bs.τ₁) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    have ht : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) Y =
        ι ψ₀ (Y + GlobalTheory.VacShape.coBar Bs Γ γ) :=
      hι.trans γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) Y
    have hs : GlobalTheory.VacShape.coBar Bs Γ γ ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ := ⟨γ, hγ, h, rfl⟩
    rw [ht, hιψ₀]
    exact hSa _ hs Y
  have hB : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      γ.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate Bs Γ X om om' hTr Y
    have hm : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) (GlobalTheory.VacShape.coBar Bs Γ x) =
        Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x γ) *
          ι ψ₀ (GlobalTheory.VacShape.coBar Bs Γ x) :=
      hι.mult γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) x hx hx0
    rw [hm, hιψ₀]
    by_cases hY : GlobalTheory.VacShape.coBar Bs Γ x ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂
    · rw [hY x hx hx0 rfl γ hγ h, one_mul]
    · rw [hBd _ hY, mul_zero]
  have hfixψ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
        (Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
          (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) • ψ₀) := by
    intro γ hγ
    rw [← hχ]
    obtain ⟨γA, hγA, γB, hγB, rfl, hA0, hB0⟩ := GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts Bs Γ X om om' hTr L₁ L₂ γ hγ
    have e0 : GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (γA + γB) =
        GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA + GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB := map_add _ _ _
    have hc := schr_schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA)
      (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB)
    have hφA : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA) φ₀ = φ₀ := by
      rw [hφ₀ γA hγA, hχ1 γA (hat γA hγA) (Or.inl hA0), one_smul]
    have hφB : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB) φ₀ = φ₀ := by
      rw [hφ₀ γB hγB, hχ1 γB (hat γB hγB) (Or.inr hB0), one_smul]
    have h1 := hc φ₀
    rw [hφB, hφA, ← e0, hφ₀ _ hγ, smul_smul] at h1
    have h2 := hc ψ₀
    rw [hB γB hγB hB0, hA γA hγA hA0, ← e0] at h2
    have key := phase hne h1 h2
    have := hacts _ (hat _ hγ) ψ₀
    rwa [key] at this
  obtain ⟨c, hc⟩ := huniq ψ₀ hψ₀ hfixψ
  exact ⟨c, by rw [← hιψ₀, hc, map_smul]⟩

end GlobalTheory.VacUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPreservingOperatorLocalStructure
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.FinComm

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eventually_int (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem pure_update (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  have hfin := finite_mulSupport _ hφ' x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin, Function.update_self]
  have : (∏ᶠ (u) (_ : u ≠ v), Function.update φ v g u (fun i => evFin F u (x i))) =
      ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i)) :=
    finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]
  rw [this]
  ring

theorem pure_update_zero (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) : pure f (Function.update φ v 0) = 0 := by
  funext x
  rw [pure_update f φ hφ]
  simp

theorem pure_update_add (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) (g h : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (g + h)) = pure f (Function.update φ v g) + pure f (Function.update φ v h) := by
  funext x
  simp only [Pi.add_apply, pure_update f φ hφ]
  ring

theorem pure_update_smul (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) (a : ℂ) (g : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (a • g)) = a • pure f (Function.update φ v g) := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, pure_update f φ hφ]
  ring

end Pure

variable {F : Type} [Field F] [NumberField F]

theorem at_of_mem_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

theorem commutant_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ A : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), (∀ Φ ∈ schA F (Fin n × Fin d), A Φ ∈ schA F (Fin n × Fin d)) →
    (∀ (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
      ∀ Φ ∈ schA F (Fin n × Fin d), A (M.co.rho B.ψ w Φ) = M.co.rho B.ψ w (A Φ)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = M.vac v) → ∃ f₁ : SInf F (Fin n × Fin d), A (pure f φ) = pure f₁ φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM A hA hcomm f φ hφSB hφv
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hvacSB : ∀ u, M.vac u ∈ SB _ := fun u => (hM.vac u).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.weil_rep_lattice_scalar_action M B.ψ hM
  have hpv : pure f M.vac ∈ schA F _ := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f M.vac hvacSB hvacO
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.weil_rep_scalar_char_of_signature B X W M r s r' s' hB hX hW hM c hc (A (pure f M.vac)) (hA _ hpv)
    fun v γ hγ => by rw [← hcomm v γ (at_of_mem_latAtV hγ) _ hpv, hc v γ hγ f, map_smul]
  have key : ∀ S : Finset (Pl F), ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) →
      (∀ v ∉ S, φ v = M.vac v) → A (pure f φ) = pure f₁ φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro φ _ h
      obtain rfl : φ = M.vac := funext fun v => h v (Finset.notMem_empty v)
      exact hf₁
    | insert v S hvS ih =>
      intro φ hSB hS
      have h0SB : ∀ u, Function.update φ v (M.vac v) u ∈ SB _ := fun u => by
        by_cases h : u = v
        · subst h; rw [Function.update_self]; exact hvacSB u
        · rw [Function.update_of_ne h]; exact hSB u
      have h0S : ∀ u ∉ S, Function.update φ v (M.vac v) u = M.vac u := fun u hu => by
        by_cases h : u = v
        · subst h; rw [Function.update_self]
        · rw [Function.update_of_ne h]; exact hS u (by simp [h, hu])
      have h0O : ∀ᶠ u in cofinite, Function.update φ v (M.vac v) u = indO u := by
        filter_upwards [hvacO, S.finite_toSet.compl_mem_cofinite] with u hu huS
        rw [h0S u huS, hu]
      have hIH := ih _ h0SB h0S
      have hmem0 := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f _ h0SB h0O
      obtain ⟨hc1, hne⟩ := GlobalTheory.T.standard_char_continuous_nontrivial B.ψ hB.std v
      have hφv : φ v ∈ Submodule.span ℂ (Set.range fun p => locOp B.ψ v p (M.vac v)) :=
        GlobalTheory.T.local_span_translates_of_nonzero_schwartz B.ψ v hc1 hne (M.vac v) (φ v) (hvacSB v) (hM.vac v).2.1 (hSB v)
      have hφeq : φ = Function.update (Function.update φ v (M.vac v)) v (φ v) := by
        rw [Function.update_idem, Function.update_eq_self]
      have step : ∀ g ∈ Submodule.span ℂ (Set.range fun p => locOp B.ψ v p (M.vac v)),
          A (pure f (Function.update (Function.update φ v (M.vac v)) v g)) =
            pure f₁ (Function.update (Function.update φ v (M.vac v)) v g) := by
        intro g hg
        induction hg using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨p, rfl⟩ := hg
          obtain ⟨w, hw, hwp⟩ := GlobalTheory.T.exists_local_point_model_eval M v p
          have e1 := GlobalTheory.T.weil_rep_pure_tensor_local M B.ψ v w hw f _ h0O
          have e2 := GlobalTheory.T.weil_rep_pure_tensor_local M B.ψ v w hw f₁ _ h0O
          rw [hwp, Function.update_self, Function.update_idem] at e1 e2
          simp only [Function.update_idem]
          rw [← e1, hcomm v w hw _ hmem0, hIH, e2]
        | zero => rw [pure_update_zero f _ h0O, pure_update_zero f₁ _ h0O, map_zero]
        | add g h _ _ hg hh =>
          rw [pure_update_add f _ h0O, pure_update_add f₁ _ h0O, map_add, hg, hh]
        | smul a g _ hg => rw [pure_update_smul f _ h0O, pure_update_smul f₁ _ h0O, map_smul, hg]
      rw [hφeq]
      exact step _ hφv
  have hfin : {v | φ v ≠ M.vac v}.Finite := Filter.eventually_cofinite.mp hφv
  exact ⟨f₁, key hfin.toFinset φ hφSB fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)⟩

end GlobalTheory.FinComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_mem_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v, φ v ∈ SB _) (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) : pure f φ ∈ schA F _ := by
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {B : Base F E}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ :=
  Submodule.span_le.2 (by
    rintro _ ⟨f, -, φ, h1, h2, rfl⟩
    exact pure_mem_schA hM f φ h1 h2)

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem comp_ev_mem_adm {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (hE : IsEv B M M₁ ι ι' I e)
    {l : Fn F n₁ d₁ →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) :
    l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have key := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  induction key using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨φ, h1, h2, rfl⟩ := hp
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := (h2.and hM.std).mono fun v h => h.1.trans h.2.symm
    have hψSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (h1 v)
    have hψstd : ∀ᶠ v in cofinite, ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM₁.std).mono fun v h => by rw [h.1, (hev v).1, h.2]
    obtain ⟨T, hT⟩ := hl _ ⟨isLocallyConstant_finprod_evalV _ hψSB hψstd,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ hψSB hψstd⟩
    refine ⟨T.comp ei, fun f => ?_⟩
    have h := hloc f φ h1 hvac
    rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l h
  | zero =>
    refine ⟨0, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) 0 = 0 := by
      funext x; simp [pureA]
    rw [this, map_zero, ContinuousLinearMap.zero_apply]
  | add p q _ _ hp hq =>
    obtain ⟨T₁, h₁⟩ := hp
    obtain ⟨T₂, h₂⟩ := hq
    refine ⟨T₁ + T₂, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (p + q) = pureA F f p + pureA F f q := by
      funext x; simp [pureA, mul_add]
    rw [this, map_add, h₁, h₂, ContinuousLinearMap.add_apply]
  | smul c p _ hp =>
    obtain ⟨T, hT⟩ := hp
    refine ⟨c • T, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (c • p) = c • pureA F f p := by
      funext x; simp [pureA]; ring
    rw [this, map_smul, hT, ContinuousLinearMap.smul_apply]

def schrLin {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := schr ψ w Φ
  map_add' Φ Ψ := by funext x; simp [schr, mul_add]
  map_smul' c Φ := by funext x; simp [schr]; ring

theorem schrLin_apply {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) : schrLin ψ w Φ = schr ψ w Φ := rfl

theorem schr_mem_schA {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have : schA F κ ≤ (schA F κ).comap (schrLin ψ w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
    show schrLin ψ w (pureA F f g) ∈ schA F κ
    rw [schrLin_apply, hT]
    exact Submodule.subset_span ⟨T f, g', hg', rfl⟩
  exact this hΦ

theorem comp_schr_mem_adm {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ schrLin ψ w ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
  obtain ⟨L, hL⟩ := hl g' hg'
  refine ⟨L.comp T, fun f => ?_⟩
  rw [LinearMap.comp_apply, schrLin_apply, hT, hL, ContinuousLinearMap.comp_apply]

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

theorem coneTerm_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ Φ ∈ PolData B G.M, ∀ h, AEStronglyMeasurable (fun g => thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))) G.M.μ := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ X om om' om₁ om₁' hT _ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ _ _ hM₂ hE Φ hΦ h
  have hM := hT.geo.hM
  have hψ := hT.base.std
  have hW : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om :=
    hT.weil
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin (a + b))
  have hl := comp_schr_mem_adm hψ (G.M.co.e (shiftA H₀ H' 1)) (comp_ev_mem_adm hM hM₂ hE hl₀)
  have hΦA := polData_le_schA hM hΦ
  have hc := hW.2.2 _ hl Φ hΦA
  have hsplit := hW.isUSplitting
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  refine Continuous.aestronglyMeasurable ?_
  have heq : (fun g => thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))) =
      fun g => ((l₀ ∘ₗ e₂) ∘ₗ schrLin B.ψ (G.M.co.e (shiftA H₀ H' 1))) (om (g, h) Φ) := by
    funext g
    have h1 : om (g, h) Φ ∈ schA F _ := hsplit.pres (g, h) Φ hΦA
    have h2 := schr_mem_schA hψ (G.M.co.e (shiftA H₀ H' 1)) h1
    have h3 := hE.maps _ h2
    exact (hl₀eq _ h3).symm
  rw [heq]
  exact hc.comp (continuous_id.prodMk continuous_const)

end GlobalTheory.ConeMeasV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartzStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitting_preserves_local_schwartz : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl F) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  first | exact @GlobalTheory.LocSplitOp.exists_locOp | exact GlobalTheory.LocSplitOp.exists_locOp | (intros; apply GlobalTheory.LocSplitOp.exists_locOp <;> assumption)
end

