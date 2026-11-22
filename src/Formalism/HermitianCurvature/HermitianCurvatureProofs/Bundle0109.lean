import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0107

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
section
open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExOf

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

theorem side {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n r : ℕ}
    {z e : Fin (2 * r + (n + 1) + 1) → ℂ} {π : Mx (n + 1) r → (W →L[ℂ] W)} {u : ℕ → ℝ} {β : ℂ}
    {L : Fin (n + 1) → ℤ} (hz : inWb (n + 1) r z) (hT : 0 < Tz (n + 1) r z) (hty : IsType (n + 1) r z π u)
    (hL : StrictAnti L)
    (hu : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ))
    (he : inWb (n + 1) r e) (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1)
    {Bs₀ : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ} (hB₀ : IsFrameOf (n + 1) r [z, e] Bs₀) :
    GlRel (EB π Bs₀) ∧ DirectSum.IsInternal (fun M : {M : Fin n → ℤ // Box L M} => CapSp (EB π Bs₀) (shf β M.1)) ∧
      ∀ M : {M : Fin n → ℤ // Box L M}, CapSp (EB π Bs₀) (shf β M.1) ≠ ⊥ ∧
        ∀ S' : Submodule ℂ W, S' ≤ CapSp (EB π Bs₀) (shf β M.1) → Stab (EB π Bs₀) S' →
          S' = ⊥ ∨ S' = CapSp (EB π Bs₀) (shf β M.1) := by
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := frame_general_linear W (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (lie_stabilizer W (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := branching_algebraic W n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  exact ⟨(frame_general_linear W (n + 1) r n z π Bs₀ hR (FrameExtension.frame_weaken hB₀)).1, hint, hS⟩

theorem labels {n r : ℕ} {T T' : ℝ} {u u' : ℕ → ℝ} (hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK)
    (ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (L L' : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hL' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ)) :
    ∃ lab : Fin n → ℤ, Box L lab ∧ Box L' lab ∧
      SDec (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) ∧
      ∀ Y : ℂ, cpol (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) =
        Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y := by
  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  choose N hN using fun j : Fin n => Qx8.rho_int hOK ρ ((j : ℕ) + 1) (hmem j)
  have hN' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) = (N j : ℝ) + u 1 + 1 / 2 := fun j => by
    have := hN j
    change M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 - 1 / 2 = (N j : ℝ) at this
    linarith
  have hI := types_interlace _ hOK ρ
  have hI' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u ((j : ℕ) + 1) ∧
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u' ((j : ℕ) + 1) ∧ u ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) ∧
      u' ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) := fun j => hI _ (hmem j)
  refine ⟨fun j => N j + 1, ?_, ?_, ?_, ?_⟩
  · intro j
    have h1 := hL j.succ
    have h2 := hL j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hN' j
    constructor
    · have : (L j.succ : ℝ) < ((N j + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((N j + 1 : ℤ) : ℝ) ≤ (L j.castSucc : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · intro j
    have h1 := hL' j.succ
    have h2 := hL' j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hN' j
    constructor
    · have : (L' j.succ : ℝ) < ((N j + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((N j + 1 : ℤ) : ℝ) ≤ (L' j.castSucc : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · intro a b hab
    have hlt := Qx8.rho_anti hOK ρ ((a : ℕ) + 1) ((b : ℕ) + 1) (by omega) (by simp only [Fin.lt_def] at hab; omega)
      (by show (b : ℕ) + 1 ≤ n + 1 - 1; omega)
    have ha := hN' a
    have hb := hN' b
    have hNab : N b < N a := by
      have : (N b : ℝ) < (N a : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨(N a - N b - 1).toNat, ?_⟩
    have h1 : (((N a - N b - 1).toNat : ℕ) : ℤ) = N a - N b - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((N a - N b - 1).toNat : ℕ) : ℂ) = ((N a - N b - 1 : ℤ) : ℂ) := by exact_mod_cast h1
    simp only [shf]
    rw [h2]
    push_cast
    ring
  · intro Y
    unfold M.xC cpol
    rw [show (⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1 = n from rfl, ProductIntervalFrames.prod_Icc_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h4 : (M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) : ℂ) = (N j : ℂ) + (u 1 : ℂ) + 1 / 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (hN' j)
      push_cast at this
      exact this
    simp only [shf]
    rw [h4]
    push_cast
    ring

theorem lie_existence_of_iso_group : KLExistsOf := by
  intro hIso hLG Wp Wq _ _ _ _ _ _ P
  obtain ⟨k, r, T, T', u, u'⟩ := P
  intro z z' π π' hPl hk
  have hk' : 2 ≤ k := hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  intro g hg hGG Fr hFr ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', hπ, hπ'⟩ := id hPl
  have hT : 0 < Tz (n + 1) r z := by
    have h2 : Tz (n + 1) r z = T := hTz
    rw [h2]; exact hOK.T_pos
  have hT' : 0 < Tz (n + 1) r z' := by
    have h2 : Tz (n + 1) r z' = T' := hTz'
    rw [h2]; exact hOK.T'_pos
  obtain ⟨-, hrep, hcont, -, -, -⟩ := id hπ
  obtain ⟨-, hrep', hcont', -, -, -⟩ := id hπ'
  obtain ⟨e', f, -, -, -, -, -, -, -, -, ⟨he'W, he'z, he'e⟩, ⟨hfW, hfz, hff⟩, hFr1, hFr2⟩ :=
    KLAM.geom_fr hz hz' hT hT' hg hGG hFr

  have hIcc : ∀ j : Fin (n + 1), (j : ℕ) + 1 ∈ Finset.Icc 1 (n + 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by omega⟩
  choose L hL using fun j : Fin (n + 1) => hOK.int_u ((j : ℕ) + 1) (hIcc j)
  choose L' hL' using fun j : Fin (n + 1) => hOK.int_u' ((j : ℕ) + 1) (hIcc j)
  have hL2 : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ) := hL
  have hL2' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ) := hL'
  have hgap : ∀ j : Fin n, max (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1)) + 1 / 2 ≤
      min (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1)) - 1 / 2 := fun j =>
    hOK.gap ((j : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩)
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2 j.castSucc
    have h2 := hL2 j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_left (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_left (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L j.succ : ℝ) < (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti' : StrictAnti L' := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2' j.castSucc
    have h2 := hL2' j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_right (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_right (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L' j.succ : ℝ) < (L' j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2 j)
    rw [hβ, ← h]
    ring
  have hrel' : ∀ j : Fin (n + 1), (u' ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L' j : ℂ) := fun j => by
    have h : (u' ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L' j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2' j)
    rw [hβ, ← h]
    ring
  obtain ⟨M, hbox, hbox', hsd, hcp⟩ := labels hOK ρ L L' hL2 hL2'
  have hfin : Finite {M : Fin n → ℤ // Box L' M} := by
    refine Finite.of_injective (β := ∀ j : Fin n, Finset.Ioc (L' j.succ) (L' j.castSucc))
      (fun M j => ⟨M.1 j, Finset.mem_Ioc.2 (M.2 j)⟩) ?_
    intro M₁ M₂ h
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun h j)
  letI : Fintype {M : Fin n → ℤ // Box L' M} := Fintype.ofFinite _

  obtain ⟨hgl', hint', hS'⟩ := side hz' hT' hπ' hanti' hrel' he'W he'z he'e hFr1
  obtain ⟨hgl, -, hS⟩ := side hz hT hπ hanti hrel hfW hfz hff hFr2
  set Mb : {M : Fin n → ℤ // Box L M} := ⟨M, hbox⟩ with hMb
  set Mb' : {M : Fin n → ℤ // Box L' M} := ⟨M, hbox'⟩ with hMb'
  set E := EB π (fun a => g *ᵥ Fr a) with hE
  set E' := EB π' Fr with hE'
  have hstabs' : ∀ (j : {M : Fin n → ℤ // Box L' M}) (a b : Fin n), ∀ v ∈ CapSp E' (shf β j.1), E' a b v ∈ CapSp E' (shf β j.1) :=
    fun j a b => (capelli_stabilizer Wq n E' (shf β j.1) hgl').1 a b
  have hstab : Stab E (CapSp E (shf β M)) := (capelli_stabilizer Wp n E (shf β M) hgl).1
  have hstab' : Stab E' (CapSp E' (shf β M)) := (capelli_stabilizer Wq n E' (shf β M) hgl').1
  obtain ⟨A, hA0, hAi⟩ := hIso (CapSp E (shf β M)) (CapSp E' (shf β M)) n (resE E _ hstab) (resE E' _ hstab')
    (shf β M) (glRel_resE hgl _ hstab) (glRel_resE hgl' _ hstab') (irr_resE _ hstab (hS Mb).1 (hS Mb).2)
    (irr_resE _ hstab' (hS' Mb').1 (hS' Mb').2) hsd (cap_resE (shf β M) hstab) (cap_resE (shf β M) hstab')

  set p : Wq →ₗ[ℂ] CapSp E' (shf β M) := projI hint' Mb' with hp
  have hpE : ∀ a b v, p (E' a b v) = resE E' _ hstab' a b (p v) := fun a b v =>
    projI_comm hint' (E' a b) (fun j => hstabs' j a b) Mb' v
  set Xl : Wq →ₗ[ℂ] Wp := (CapSp E (shf β M)).subtype ∘ₗ (A ∘ₗ p) with hXl
  set X : Wq →L[ℂ] Wp := LinearMap.toContinuousLinearMap Xl with hX
  have hXv : ∀ v, X v = (A (p v) : Wp) := fun v => by
    rw [hX, LinearMap.coe_toContinuousLinearMap']
    rfl
  have hAv : ∀ a b x, A (resE E' _ hstab' a b x) = resE E _ hstab a b (A x) := fun a b x =>
    LinearMap.congr_fun (hAi a b) x
  have hXint : ∀ (a b : Fin n) (v : Wq), X (EB π' Fr a b v) = EB π (fun i => g *ᵥ Fr i) a b (X v) := by
    intro a b v
    rw [hXv, hXv]
    change (A (p (E' a b v)) : Wp) = E a b (A (p v) : Wp)
    rw [hpE, hAv, resE_apply]
  refine ⟨X, hLG Wp Wq (n + 1) r z z' π π' hz hz' hT hT' ⟨hrep, hcont⟩ ⟨hrep', hcont'⟩ g hg hGG Fr hFr X hXint, ?_, ?_⟩
  · intro Y v
    rw [hXv, hXv]
    change (A (p (qdet E' (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) v)) : Wp) = Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y • (A (p v) : Wp)
    rw [qdet_int p hpE, cap_resE (shf β M) hstab', map_smul, Submodule.coe_smul, hcp Y]
  · intro hX0
    obtain ⟨x, hx⟩ : ∃ x, A x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hA0 (LinearMap.ext hc)
    apply hx
    have h1 : X (x : Wq) = 0 := by rw [hX0]; rfl
    rw [hXv, hp, projI_self hint' (i := Mb') x] at h1
    exact_mod_cast h1

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExOf

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem lie_existence_of_iso_group : KLExistsOf := KLExOf.lie_existence_of_iso_group

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesLeft
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep in
theorem gauge_left_line_holds : GLLeft := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk ζ hζ Fr hFr
  obtain ⟨-, hz, hz', hTz, hTz', -, -⟩ := hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hU : μ ∈ UH (Hpk P.k P.r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : μ⁻¹ ∈ UH (Hpk P.k P.r) := hGi.1
  have hT := Bs.T_pos

  set y := μ *ᵥ Bs.z' with hydef
  have hy : inWb P.k P.r y := Qx8.inWb_mulVec hG hz'
  have hyz : herm (Hpk P.k P.r) y Bs.z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' Bs.sec hζ'
  have hyy : herm (Hpk P.k P.r) y y = -((Tz P.k P.r Bs.z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hpos : 0 < Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  set p := SSn.prWv P.k P.r Bs.z y with hpdef
  have hpp := DU.prWv_norm hT hy hyy hyz
  have hre : (herm (Hpk P.k P.r) p p).re = Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [hpp]; simp
  have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ =
      (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) • p := by
    show SSn.unitH P.k P.r p = _
    unfold SSn.unitH
    rw [hre]
  have hsne : (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z') := Real.sqrt_pos.2 hpos
    exact_mod_cast (inv_pos.2 this).ne'

  have hFz : ∀ a, herm (Hpk P.k P.r) (Fr a) Bs.z = 0 := fun a => hFr.2.2 a Bs.z (by simp)
  have hFy : ∀ a, herm (Hpk P.k P.r) (Fr a) y = 0 := by
    intro a
    have h1 : herm (Hpk P.k P.r) (Fr a) (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 := hFr.2.2 a _ (by simp)
    rw [hν, DU.hsmul_r] at h1
    have h2 : herm (Hpk P.k P.r) (Fr a) p = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) hsne
      · exact h
    rw [hpdef, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFz a, mul_zero, add_zero] at h2
    exact h2
  have hmi : μ⁻¹ * μ = 1 := Gauge.GC.KLAM.inv_mul_uh hU
  have hmm : μ * μ⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  have hz'e : Bs.z' = μ⁻¹ *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hF' : Q.IsFrameOf P.k P.r [μ⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => μ⁻¹ *ᵥ Fr a) := by
    refine ⟨fun a => Qx8.inWb_mulVec hGi (hFr.1 a), fun a b => ?_, fun a w hw => ?_⟩
    · rw [Qx2.herm_uh hUi]; exact hFr.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rw [Qx2.herm_uh hUi]; exact hFz a
      · rw [hz'e, Qx2.herm_uh hUi]; exact hFy a
  refine ⟨hF', fun X hX w v => ?_⟩
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX (h, h') ⟨hh, hh', he⟩
  have hint := Qx8.capRep_intertwine hF' Bs.π'_rep Bs.π'_cont hU X
    (fun h' hh' hy' u => Gauge.GC.KLAM.fib_intertwine Bs.π_rep hG hXF hh' hy' u) w v
  have hback : (fun a => μ *ᵥ (μ⁻¹ *ᵥ Fr a)) = Fr := by
    funext a
    rw [Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  rw [hint, hback]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

def sig (TT : ℝ) (ζ : ℂ) : ℂ := ((Real.sqrt (Complex.normSq ζ - TT) : ℝ) : ℂ)

def gg (TT : ℝ) (ζ : ℂ) : ℂ := ((Complex.normSq ζ - TT : ℝ) : ℂ)

def PS (TT : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (p : MvPolynomial (Fin 3) ℂ), ∀ ζ : ℂ, TT < Complex.normSq ζ →
    gg TT ζ ^ m * f ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] p

def PSV (TT : ℝ) {V : Type*} [AddCommGroup V] [Module ℂ V] (f : ℂ → V) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ → ℂ) (v : Fin n → V), (∀ i, PS TT (a i)) ∧
    ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = ∑ i, a i ζ • v i

def rot (θ : ℝ) (ζ : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * ζ

def PolynomialRadialAtSection : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def Transfer : Prop := SSn.Rep.ThtFacts → PolynomialRadialAtSection → PolyRadialS

def DatumConst : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ ζ₁ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → Tz k r z * Tz k r z' < Complex.normSq ζ₁ →
      SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ = SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ₁ ∧
      SSn.nu0' k r z z' (TheSec.theSection k r z z') ζ = SSn.nu0' k r z z' (TheSec.theSection k r z z') ζ₁ ∧
      SSn.io0 k r z z' (TheSec.theSection k r z z') ζ = SSn.io0 k r z z' (TheSec.theSection k r z z') ζ₁

def KapLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), Gauge.GC.KapPt P Bs d Qr ∧
      ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ ρ : M.Ty P,
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf.comp (Qr ρ)

def FibStable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ ρ : M.Ty P,
      (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ ∧
      (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ

def AlgSS : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜), d.Rel →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ Y : ℂ,
      d.κ (Pi.single ρ 1) * d.QQ Y 1 0 * d.κ (Pi.single π 1) = M.xEx P {l} π Y • (d.SS l * d.κ (Pi.single π 1))

def CorePoly : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ Y : ℂ, PSV P.TT (fun ζ =>
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def PhaseInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ θ : ℝ, ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp (S (rot θ ζ) Xf) = c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) ∧
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ)) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ)) Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def PhaseExtract : Prop :=
  ∀ (TT : ℝ) (f : ℂ → ℂ), 0 < TT → PS TT f → (∀ θ : ℝ, ∀ ζ : ℂ, TT < Complex.normSq ζ → f (rot θ ζ) = f ζ) →
    ∃ (m : ℕ) (q : Polynomial ℂ), ∀ ζ : ℂ, TT < Complex.normSq ζ → gg TT ζ ^ m * f ζ = q.eval (sig TT ζ)

def TWNe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ ζ ∈ Gauge.GC.Ann P,
    ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf → Xf ≠ 0 →
      (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) ≠ 0

def PolynomialRadialAtSectionOfPhaseInvariance : Prop :=
  DatumConst → KapLine → FibStable → AlgSS → CorePoly → PhaseInv → PhaseExtract → TWNe → PolynomialRadialAtSection

def PolyRadialSOfCut : Prop :=
  SSn.Rep.ThtFacts → Transfer → DatumConst → KapLine → FibStable → AlgSS → CorePoly → PhaseInv → PhaseExtract → TWNe →
    PolyRadialS

theorem polynomialRadial_of_base (h0 : PolynomialRadialAtSectionOfPhaseInvariance) : PolyRadialSOfCut :=
  fun hT hTr hD hK hF hA hC hP hE hW => hTr hT (h0 hD hK hF hA hC hP hE hW)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocTail
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem GermD.germLoc_tail (hG : GermD s β ε Y ut bt SS) (Gk : ι × ℂ → ι × ℂ → ℂ)
    (hGk : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Gk (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x'))
    (hatB : ℂ → ι → ι → ℂ) (hN : ∀ σ : ℂ, ∀ h ∈ Y, ∀ h' ∈ Y, Nhat s β bt σ h h' = hatB σ h h') :
    (∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z => ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ)) ∧
    ∃ Pua Paa : ι × ℂ → ι × ℂ → ℂ,
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) Gk Pua Paa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖Paa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
        Tendsto (fun x => Paa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => Pua (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => conj (Pua (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hatB σ h h')) := by
  obtain ⟨h0, h1, h2, h3⟩ := hG.propG
  refine ⟨fun h hh h' hh' => integrable_inner_of_memLp (h0 h hh).1 (h0 h' hh').1,
    gramL volume (Uc s ut) (Ac s β ε bt), gramL volume (Ac s β ε bt) (Ac s β ε bt),
    fun Xs hXs => ?_, h2, fun h hh h' hh' σ => ?_⟩
  · have hb := h1 Xs hXs
    unfold KB.BlockPSD TB.PSDOn at hb ⊢
    open scoped ComplexOrder in
    refine (congrArg Matrix.PosSemidef ?_).mpr hb
    ext i j
    obtain ⟨x, hx⟩ := i
    obtain ⟨y, hy⟩ := j
    rcases x with p | q <;> rcases y with p' | q'
    · have hp := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hx)
      have hp' := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hy)
      show Gk p p' = gramL volume (Uc s ut) (Uc s ut) p p'
      exact hGk p.1 hp.1 p'.1 hp'.1 p.2 p'.2 (hXs _ hp.2) (hXs _ hp'.2)
    · rfl
    · rfl
    · rfl
  · rw [← hN σ h hh h' hh']
    exact h3 h hh h' hh' σ

end

end Formalism.FourierDecayAlt.P.PBK
end

