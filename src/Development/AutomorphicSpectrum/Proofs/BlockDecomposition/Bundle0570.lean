import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0541
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.Holo

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

open GlobalTheory.QCoh.Qcqs in

theorem baseRingHom_toSpecΓ {Y : Scheme.{0}} {B : CommRingCat.{0}} (ψ : B ⟶ Γ(Y, ⊤)) :
    baseRingHom (Y.toSpecΓ ≫ Spec.map ψ) ⊤ = ψ := by
  rw [baseRingHom_comp_SpecMap, baseRingHom_top, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

section Chart

variable (c : ∀ k, Bk n k)

abbrev CoordIdx := {q : Σ k, Bk n k // q.2 ≠ c q.1}

abbrev CRing := MvPolynomial (CoordIdx c) ℤ

abbrev CSpec : Scheme.{0} := Spec (.of (CRing c))

def coordVal (k : Fin (m + 1)) (j : Bk n k) : CRing c :=
  if h : j = c k then 1 else X ⟨⟨k, j⟩, h⟩

def chartMap (k : Fin (m + 1)) : CSpec c ⟶ PSpace ℤ (n k) :=
  ofChartHom (c k) (CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (c k))) (S := CRing c)
    (chartLift (c k) (Int.castRingHom _) (coordVal c k)) ≫ (Scheme.ΓSpecIso (.of (CRing c))).inv)

theorem chartMap_top (k : Fin (m + 1)) : ⊤ ≤ chartMap c k ⁻¹ᵁ chart ℤ (n k) (c k) := ofChartHom_preimage _ _

theorem coordVal_self (k : Fin (m + 1)) : coordVal c k (c k) = 1 := dif_pos rfl

theorem pullRatio_chartMap (k : Fin (m + 1)) (j : Bk n k) :
    pullRatio (chartMap c k) ⊤ (c k) (chartMap_top c k) j =
      (Scheme.ΓSpecIso (.of (CRing c))).inv.hom (coordVal c k j) :=
  by
  have e : (chartMap c k).appLE (chart ℤ (n k) (c k)) ⊤ (chartMap_top c k) = _ := ofChartHom_appLE (c k) _
  unfold pullRatio
  rw [e]
  exact congrArg (Scheme.ΓSpecIso (.of (CRing c))).inv.hom (chartLift_ratio (c k) _ (coordVal_self c k) j)

open GlobalTheory.QCoh.Qcqs in
theorem pullRatio_comp_chartMap {Z : Scheme.{0}} (w : Z ⟶ CSpec c) (k : Fin (m + 1))
    (h : ⊤ ≤ (w ≫ chartMap c k) ⁻¹ᵁ chart ℤ (n k) (c k)) (j : Bk n k) :
    pullRatio (w ≫ chartMap c k) ⊤ (c k) h j = (baseRingHom w ⊤).hom (coordVal c k j) := by
  have := appLE_pullRatio (φ := chartMap c k) (W := ⊤) (i := c k) (hi := chartMap_top c k) (j := j) w
    (T := ⊤) le_top
  rw [pullRatio_chartMap] at this
  exact this.symm

def tau : CSpec c ⟶ MP ℤ m n :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (specZIsTerminal.from _) (chartMap c)
    fun _ => specZIsTerminal.hom_ext _ _

theorem tau_pr (k : Fin (m + 1)) : tau c ≫ prB n k = chartMap c k :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr m n _ _ _ k

theorem tau_le : ⊤ ≤ tau c ⁻¹ᵁ mchart c := fun x _ => Set.mem_iInter.2 fun k => by
  have h := chartMap_top c k (Set.mem_univ x)
  rw [← tau_pr] at h
  exact h

def rho : CRing c →+* Γ(MP ℤ m n, mchart c) :=
  (dehomog c).comp (rename (R := ℤ) (Subtype.val : CoordIdx c → Σ k, Bk n k)).toRingHom

theorem rho_coordVal (k : Fin (m + 1)) (j : Bk n k) :
    rho c (coordVal c k j) = pullRatio (prB n k) (mchart c) (c k) (mchart_le c k) j := by
  by_cases h : j = c k
  · subst h
    rw [coordVal_self, map_one, pullRatio_self]
  · rw [coordVal, dif_neg h]
    simp only [rho, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, dehomog, eval₂Hom_X']
    exact resG_pullRatio _

theorem tau_rho_coordVal (k : Fin (m + 1)) (j : Bk n k) :
    ((tau c).appLE (mchart c) ⊤ (tau_le c)).hom (rho c (coordVal c k j)) =
      (Scheme.ΓSpecIso (.of (CRing c))).inv.hom (coordVal c k j) := by
  rw [rho_coordVal, appLE_pullRatio, ← pullRatio_chartMap]
  exact pullRatio_of_eq (tau_pr c k) _ _

theorem tau_comp_rho :
    CommRingCat.ofHom (rho c) ≫ (tau c).appLE (mchart c) ⊤ (tau_le c) =
      (Scheme.ΓSpecIso (.of (CRing c))).inv := by
  ext1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
  · have e : (C r : CRing c) = ((r : ℤ) : CRing c) := map_intCast C r
    rw [e]
    exact (map_intCast _ r).trans (map_intCast _ r).symm
  · obtain ⟨⟨k, j⟩, h⟩ := q
    have e : (X ⟨⟨k, j⟩, h⟩ : CRing c) = coordVal c k j := by
      rw [coordVal, dif_neg (show ¬ j = c k from h)]
    rw [e]
    exact tau_rho_coordVal c k j

def toC : (mchart c).toScheme ⟶ CSpec c :=
  (mchart c).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (rho c) ≫ (mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge)

open GlobalTheory.QCoh.Qcqs in
theorem baseRingHom_toC : baseRingHom (toC c) ⊤ =
    CommRingCat.ofHom (rho c) ≫ (mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge :=
  baseRingHom_toSpecΓ _

open GlobalTheory.QCoh.Qcqs in
theorem toC_tau : toC c ≫ tau c = (mchart c).ι := by
  refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
  have e : (toC c ≫ tau c) ≫ prB n k = toC c ≫ chartMap c k := by rw [Category.assoc, tau_pr]
  have h₀ : ⊤ ≤ (toC c ≫ chartMap c k) ⁻¹ᵁ chart ℤ (n k) (c k) :=
    le_trans le_top ((toC c).preimage_mono (chartMap_top c k))
  have h₂ : ⊤ ≤ ((mchart c).ι ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) (c k) :=
    le_trans (mchart c).ι_preimage_self.ge ((mchart c).ι.preimage_mono (mchart_le c k))
  refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ => ⟨⊤, trivial, c k, e ▸ h₀, h₂, fun j => ?_⟩
  rw [pullRatio_of_eq e _ h₀, pullRatio_comp_chartMap, baseRingHom_toC]
  refine (congrArg ((mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge).hom (rho_coordVal c k j)).trans ?_
  exact appLE_pullRatio _ _

end Chart

open GlobalTheory.QCoh.Qcqs in

theorem affine_surj (c : ∀ k, Bk n k) : IsAffineOpen (mchart c) ∧ Function.Surjective (dehomog c) := by
  have hr : Set.range (tau c) ⊆ Set.range (mchart c).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact tau_le c (Set.mem_univ x)
  let τ' : CSpec c ⟶ (mchart c).toScheme := IsOpenImmersion.lift (mchart c).ι (tau c) hr
  have hτ : τ' ≫ (mchart c).ι = tau c := IsOpenImmersion.lift_fac _ _ _
  have h1 : toC c ≫ τ' = 𝟙 _ := by
    rw [← cancel_mono (mchart c).ι, Category.assoc, hτ, toC_tau, Category.id_comp]
  have h2 : τ' ≫ toC c = 𝟙 _ := by
    refine eq_of_baseRingHom_top ?_
    have a : baseRingHom (τ' ≫ toC c) ⊤ = (Scheme.ΓSpecIso (.of (CRing c))).inv := by
      have hle : (⊤ : (CSpec c).Opens) ≤ τ' ⁻¹ᵁ (⊤ : (mchart c).toScheme.Opens) := fun _ _ => trivial
      rw [← baseRingHom_appLE (toC c) τ' ⊤ ⊤ hle, baseRingHom_toC, Category.assoc,
        Scheme.Hom.appLE_comp_appLE]
      refine Eq.trans ?_ (tau_comp_rho c)
      exact congrArg _ (appLE_of_eq hτ _ _ _ _)
    rw [a, baseRingHom_top]
    simp
  have hi : IsIso (toC c) := ⟨τ', h1, h2⟩
  have hb : IsIso (baseRingHom (toC c) ⊤) := by
    rw [baseRingHom_top]
    have : IsIso (toC c).appTop := inferInstanceAs (IsIso (Scheme.Γ.map (toC c).op))
    infer_instance
  refine ⟨IsAffine.of_isIso (toC c), ?_⟩
  have hρ : IsIso (CommRingCat.ofHom (rho c)) := by
    rw [baseRingHom_toC] at hb
    exact IsIso.of_isIso_comp_right _ ((mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge)
  intro b
  obtain ⟨P, rfl⟩ := (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (rho c))).2 b
  exact ⟨rename Subtype.val P, rfl⟩

theorem mem_ptsIn_mchart {y : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} (c : ∀ k, Bk n k) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) ↔ ∀ k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
  ⟨fun h k => GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) h,
    fun h => GlobalTheory.CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => GlobalTheory.CxPts.mem_ptsIn.1 (h k))⟩

theorem ev_dehomog {y : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z) (c : ∀ k, Bk n k)
    (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) (P : Pol n) :
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c P) y =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) P := by
  have e : (evHom hy).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q : (Σ k, Bk n k) => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, map_intCast, eval₂Hom_C]
      have : (C r : Pol n) = (r : Pol n) := map_intCast C r
      rw [this, map_intCast, map_intCast]
      rfl
    · obtain ⟨k, j⟩ := q
      have hk := (mem_ptsIn_mchart c).1 hy k
      simp only [RingHom.comp_apply, eval₂Hom_X', dehomog]
      rw [← ev_eq hy, GlobalTheory.CxPts.ev_res _ hy]
      exact (H k (c k)).2 j hk
  rw [ev_eq hy]
  exact congrArg (fun f => f P) e

theorem differentiableOn_eval₂ {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : Set E} {g : E → ι → ℂ}
    (hg : ∀ q, DifferentiableOn ℂ (fun v => g v q) T) (P : MvPolynomial ι ℤ) :
    DifferentiableOn ℂ (fun v => eval₂Hom (Int.castRingHom ℂ) (g v) P) T := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [eval₂Hom_C] using differentiableOn_const _
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p q hp => simpa only [map_mul, eval₂Hom_X'] using hp.fun_mul (hg q)

theorem holo_near (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (hO : IsOpen O) (hγ : DifferentiableOn ℂ γ O) (hU : ∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v))
    (v₀ : Fin D → ℂ) (hv₀ : v₀ ∈ O) :
    ∃ O' : Set (Fin D → ℂ), IsOpen O' ∧ v₀ ∈ O' ∧ O' ⊆ O ∧ ContinuousOn s O' ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O' ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  have hc : ∀ k, ∃ j, γ v₀ ⟨k, j⟩ ≠ 0 := fun k =>
    ⟨ptChart _ k, ((hU v₀ hv₀) k _).1.1 (GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩
  choose c hc using hc
  have hq : ∀ q, DifferentiableOn ℂ (fun v => γ v q) O := fun q => differentiableOn_pi.1 hγ q
  let O' : Set (Fin D → ℂ) := ⋂ k, (O ∩ (fun v => γ v ⟨k, c k⟩) ⁻¹' {0}ᶜ)
  have hO' : IsOpen O' := isOpen_iInter_of_finite fun k =>
    (hq _).continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : O' ⊆ O := fun v hv => (Set.mem_iInter.1 hv 0).1
  have hne : ∀ v ∈ O', ∀ k, γ v ⟨k, c k⟩ ≠ 0 := fun v hv k => (Set.mem_iInter.1 hv k).2
  have hv₀' : v₀ ∈ O' := Set.mem_iInter.2 fun k => ⟨hv₀, hc k⟩
  obtain ⟨haff, hsurj⟩ := affine_surj c
  have hUa : IsAffineOpen (i ⁻¹ᵁ mchart c) := haff.preimage i
  have hm : ∀ v ∈ O', PtsOver.map i rfl _ (s v) ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := fun v hv =>
    (mem_ptsIn_mchart c).2 fun k => ((hU v (hsub hv)) k (c k)).1.2 (hne v hv k)
  have hs : ∀ v ∈ O', s v ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := fun v hv => hm v hv
  have hd : ∀ a : Γ(X, i ⁻¹ᵁ mchart c),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) a ∘ s) O' := by
    intro a
    obtain ⟨b, rfl⟩ := i.app_surjective (mchart c) haff a
    obtain ⟨P, rfl⟩ := hsurj b
    refine (differentiableOn_eval₂ (g := fun v q => γ v q / γ v ⟨q.1, c q.1⟩)
      (fun q => by
        simpa only [div_eq_mul_inv] using ((hq q).mono hsub).fun_mul (((hq _).mono hsub).fun_inv fun v hv => hne v hv q.1)) P).congr fun v hv => ?_
    exact (ev_app i rfl (mchart c) _ (s v)).trans (ev_dehomog (hU v (hsub hv)) c (hm v hv) P)
  obtain ⟨h1, h2⟩ := GlobalTheory.CxPts.holo_of_affine hUa hO' hs hd
  exact ⟨O', hO', hv₀', hsub, h1, h2⟩

theorem holo (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (hO : IsOpen O) (hγ : DifferentiableOn ℂ γ O) (hU : ∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v)) :
    ContinuousOn s O ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  refine ⟨fun v hv => ?_, fun W f v hv => ?_⟩
  · obtain ⟨O', h1, h2, -, h4, -⟩ := holo_near m n X i D O γ s hO hγ hU v hv
    exact (h4.continuousAt (h1.mem_nhds h2)).continuousWithinAt
  · obtain ⟨O', h1, h2, -, -, h5⟩ := holo_near m n X i D O γ s hO hγ hU v hv.1
    exact (h5 W f v ⟨h2, hv.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨O', h1, h2, fun x hx => ⟨hx.1, hx.2.2⟩⟩)

end GlobalTheory.CompanionTheory.MixZ.Holo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsumSucc
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HeckeEig

theorem hsum_succ (α β : ℂ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1 + 1), α ^ i * β ^ (j + 1 - i) =
      α ^ (j + 1) + β * ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]
    ring

theorem e2a : E2a := by
  intro k N χ a h
  obtain ⟨_, h1, hH⟩ := h
  have hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n := by
    intro p hp n _ hpn
    have := hH p n hp
    rw [if_neg hpn, add_zero] at this
    exact this.symm
  have hrec : ∀ p, p.Prime → ∀ n, 0 < n →
      a (p * (p * n)) = a p * a (p * n) - (χ p * (p : ℂ) ^ (k - 1)) * a n := by
    intro p hp n _
    have := hH p (p * n) hp
    rw [if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos] at this
    rw [this]; ring
  refine ⟨fun m n hmn => GlobalTheory.CompanionTheory.HeckeMult.apply_mul_of_coprime a
      (fun p => χ p * (p : ℂ) ^ (k - 1)) h1 hcop hrec m n hmn, ?_⟩
  intro p hp α β hs hp' j
  induction j using Nat.twoStepInduction with
  | zero => simp [h1]
  | one =>
    simp [Finset.sum_range_succ]
    rw [← hs]
    ring
  | more j ih0 ih1 =>
    have r := hH p (p ^ (j + 1)) hp
    have hd : p ^ (j + 1) / p = p ^ j := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    have hm : p * p ^ (j + 1) = p ^ (j + 2) := by ring
    rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero j)), hd, hm] at r
    have e : a (p ^ (j + 2)) = a p * a (p ^ (j + 1)) - χ p * (p : ℂ) ^ (k - 1) * a (p ^ j) := by
      rw [r]; ring
    rw [e, ih1, ih0, ← hs, ← hp', show j + 2 = j + 1 + 1 by omega, hsum_succ α β (j + 1), hsum_succ α β j]
    ring

end GlobalTheory.CompanionTheory.HeckeEig
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ)

noncomputable def rowInfEquiv : (Fin k → InfiniteAdeleRing E) ≃+ (Fin k → Cinf E) :=
  AddEquiv.piCongrRight fun _ => (infEq E).symm.toAddEquiv

theorem nuInf_isAddHaarMeasure : (nuInf E k).IsAddHaarMeasure := by
  have hc : Continuous (rowInfEquiv E k) :=
    continuous_pi fun i => (GASplit.continuous_infEq_symm E).comp (continuous_apply i)
  have hc' : Continuous (rowInfEquiv E k).symm :=
    continuous_pi fun i => (continuous_infEq E).comp (continuous_apply i)
  have hp : (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact AddEquiv.isAddHaarMeasure_map _ (rowInfEquiv E k) hc hc'

end GlobalTheory.CompanionTheory.CutOff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectivePairingFiniteFamilyStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_pairing_finite_family : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 → ∃ (d : ℕ) (a : Fin d → HermE D r), Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.Sep.exists_separating | exact GlobalTheory.CompanionTheory.WSum.Sep.exists_separating | (intros; apply GlobalTheory.CompanionTheory.WSum.Sep.exists_separating <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvSmulEqFinitePartInvSmul
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem ord_eq_ord_vw_finitePart {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    GroundTheory.Global.IdeleGroup.ord v s =
      GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v :=
  rfl

theorem coe_smul_eq_finitePart_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s) • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  refine GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _)
    (GlobalTheory.Idele.smul_ne_zero _ (Units.ne_zero _)) fun v => ?_
  rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ (Units.ne_zero _),
    ord_eq_ord_vw_finitePart]

theorem inv_smul_eq_finitePart_inv_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s⁻¹ • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  coe_smul_eq_finitePart_smul s⁻¹ 𝔞

end GlobalTheory.CompanionTheory.EllipticCM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAnalyticUniformizationOfIsAnalyticIso
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

open WeierstrassCurve GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian

theorem variableChangePoint_latticePoint {X : WeierstrassCurve ℂ} {L : PeriodPair}
    {C : VariableChange ℂ} (h : C • X = GlobalTheory.latticeCurve L) (h' : C⁻¹ • weierstrassCurve L = X)
    (z : ℂ) :
    GlobalTheory.variableChangePoint C h (GlobalTheory.latticePoint L z) = vcPoint C⁻¹ h' (toPoint L z) := by
  by_cases hz : z ∈ L.lattice
  · rw [GlobalTheory.latticePoint_of_mem L hz, toPoint_of_mem hz, map_zero, vcPoint_zero]
  · rw [GlobalTheory.latticePoint_of_notMem L hz, toPoint_of_notMem hz, GlobalTheory.variableChangePoint_some,
      vcPoint_some, Affine.Point.some.injEq]
    have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
    constructor
    · simp only [vcX, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring
    · simp only [vcY, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring

theorem isAnalyticUniformization_of_isAnalyticIso {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [Algebra K ℂ] (_h2 : Module.finrank ℚ K = 2) (X : WeierstrassCurve ℂ)
    [X.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (_h𝔞 : 𝔞 ≠ 0)
    (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub 𝔞) ≃+ X.toAffine.Point)
    (hξ : GlobalTheory.EllipticCM.IsAnalyticIso ξ) :
    GroundTheory.Global.Elliptic.IsAnalyticUniformization
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) 𝔞)
      (ξ.toAddMonoidHom.comp (QuotientAddGroup.mk' _)) := by
  obtain ⟨L, C, h⟩ := GlobalTheory.exists_variableChange_eq_latticeCurve X
  obtain ⟨α, hα, hΛ, hz⟩ := hξ.exists_mul h
  have e : GlobalTheory.latticeCurve L = weierstrassCurve L := by
    simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]
  have h' : C⁻¹ • weierstrassCurve L = X := by
    rw [← e, ← h, inv_smul_smul]
  have hΛ' : ∀ z, z ∈ idealLattice (algebraMap K ℂ) 𝔞 ↔ α * z ∈ L.lattice := fun z => by
    rw [← hΛ]
    rfl
  have hf := ((isAnalyticUniformization_toPointHom L).comp_mul hα hΛ').vcPoint C⁻¹ h'
  convert hf using 1
  ext z
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
    AddMonoidHom.coe_mulLeft]
  exact (hz z).trans (variableChangePoint_latticePoint h h' _)

end GlobalTheory.CompanionTheory.EllipticCM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedImageOfSobolevLower
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob

namespace GlobalTheory.CompanionTheory.SmoothClosed

theorem smoothVec_sub {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {u v : H}
    (hu : SmoothVec Lie σ u) (hv : SmoothVec Lie σ v) : SmoothVec Lie σ (u - v) := by
  intro k Xs hX
  simpa only [map_sub] using (hu k Xs hX).sub (hv k Xs hX)

theorem tendsto_seminorm_sub {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {q : Seminorm ℂ E} (hq : Continuous q) {u : ℕ → E} {y : E} (hu : Filter.Tendsto u Filter.atTop (nhds y)) :
    Filter.Tendsto (fun k => q (u k - y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k => u k - y) Filter.atTop (nhds (y - y)) := hu.sub_const y
  rw [sub_self] at h
  simpa [Function.comp_def, map_zero] using (hq.tendsto 0).comp h

theorem isClosed_image_of_sobolev_lower : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ → ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w)) → IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hmod T hT hlow
  haveI : FirstCountableTopology E := hmod.withSeminorms.firstCountableTopology
  refine IsSeqClosed.isClosed ?_
  intro x y hx hxy
  choose w hw hTw using hx
  have hcauchy : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ := by
    intro S hS δ hδ
    obtain ⟨q, hq, hqb⟩ := hlow S hS
    have ht := tendsto_seminorm_sub hq hxy
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hδ)))
    refine ⟨K, fun k hk m hm => ?_⟩
    calc sobNorm σ S (w k - w m) ≤ q (T (w k - w m)) := hqb _ (smoothVec_sub (hw k) (hw m))
      _ = q ((x k - y) - (x m - y)) := by rw [T.map_sub, hTw, hTw, sub_sub_sub_cancel_right]
      _ ≤ q (x k - y) + q (x m - y) := map_sub_le_add q _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hK k hk) (hK m hm)
      _ = δ := add_halves δ
  obtain ⟨w0, hw0, hconv⟩ := GlobalTheory.CompanionTheory.SobComplete.smoothVec_complete n ε H σ hU hI w hw hcauchy
  refine ⟨w0, hw0, ?_⟩
  obtain ⟨-, hT2⟩ := hT
  have hT' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds (T w0)) := by
    refine (hmod.withSeminorms.tendsto_nhds _ _).2 ?_
    intro i δ hδ
    obtain ⟨S, C, hS, hb⟩ := hT2 i
    have hC : Filter.Tendsto (fun k => C * sobNorm σ S (w k - w0)) Filter.atTop (nhds 0) := by
      simpa using (hconv S hS).const_mul C
    filter_upwards [hC.eventually (gt_mem_nhds hδ)] with k hk
    calc p i (T (w k) - T w0) = p i (T (w k - w0)) := by rw [T.map_sub]
      _ ≤ C * sobNorm σ S (w k - w0) := hb _ (smoothVec_sub (hw k) hw0)
      _ < δ := hk
  have hx' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds y) := by
    simp only [hTw]
    exact hxy
  exact tendsto_nhds_unique hT' hx'

end GlobalTheory.CompanionTheory.SmoothClosed

end
end

