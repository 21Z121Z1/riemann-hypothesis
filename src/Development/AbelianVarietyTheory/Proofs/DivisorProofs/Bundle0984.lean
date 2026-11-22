import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0881
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralHeckeElementExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeCompl

open Formalism.L2.NTheta (IsIdemAt IsHeckeElt LamHat)
open Formalism.IndefR.Bridge (IsDC)
open scoped Matrix

theorem isDC_of_local {G : Type} [Group G] {J L : Subgroup G} {x : G} {R : Finset G} (hx : x ∈ L) (hR : ∀ γ ∈ R, γ ∈ L)
    (hs : ∀ k ∈ J, ∃ a ∈ J, ∃ b ∈ J, a ∈ L ∧ Commute x b ∧ k = a * b)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, γ = k₁ * x * k₂)
    (h2 : ∀ y : G, (∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, y = k₁ * x * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * y ∈ J ⊓ L) : IsDC J x R := by
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := h1 γ hγ
    exact ⟨⟨k₁, hk₁.1⟩, ⟨k₂, hk₂.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, hc, e⟩ := hs k₁ k₁.2
    obtain ⟨γ, ⟨hγ, hγJ⟩, hu⟩ := h2 (a * x) ⟨a, ⟨ha, haL⟩, 1, Subgroup.one_mem _, by simp⟩
    have eg : (k₁ : G) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, ← hc.eq]; group
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · rw [eg, ← mul_assoc]
      exact J.mul_mem hγJ.1 (J.mul_mem hb k₂.2)
    · rintro δ ⟨hδ, hδJ⟩
      refine hu δ ⟨hδ, ?_, L.mul_mem (L.inv_mem (hR δ hδ)) (L.mul_mem haL hx)⟩
      have := J.mul_mem hδJ (J.inv_mem (J.mul_mem hb k₂.2))
      rw [eg] at this
      simpa [mul_assoc] using this

theorem idem_pow {A : Type} [CommRing A] {e s p : A} (h : e * s = e * p) (n : ℕ) : e * s ^ n = e * p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    linear_combination s * ih + p ^ n * h

theorem det_compl {A : Type} [CommRing A] {e s p d d' u u' : A} {n k : ℕ} (hk : k ≤ n) (h : e * s = e * p)
    (hd : d * d' = 1) (hu : e * u * u' = e) (h5 : e * d = e * p ^ k * u) :
    e * (s ^ n * d') = e * p ^ (n - k) * u' := by
  have h1 := idem_pow h n
  have h2 : p ^ n = p ^ (n - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [h2] at h1
  linear_combination d' * h1 - (p ^ (n - k) * p ^ k * d') * hu - (p ^ (n - k) * u' * d') * h5 +
    (e * p ^ (n - k) * u') * hd

theorem vec_upper {R : Type} [CommRing R] {n : ℕ} {M M' : Matrix (Fin n) (Fin n) R} (hM : M' * M = 1) {e s p : R}
    (h : e * s = e * p) {y z : Fin n → R} (hy : (fun a => e * (p * y a)) = fun a => e * M.mulVec z a) :
    (fun a => e * (s • M').mulVec y a) = fun a => e * z a := by
  have h1 : e • p • y = e • M *ᵥ z := hy
  change e • (s • M') *ᵥ y = e • z
  rw [Matrix.smul_mulVec, smul_smul, h, ← Matrix.mulVec_smul, mul_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec]

theorem vec_lower {R : Type} [CommRing R] {n : ℕ} {M M' : Matrix (Fin n) (Fin n) R} (hM : M' * M = 1) {e s p : R}
    (he : e * e = e) (h : e * s = e * p) (y : Fin n → R) :
    (fun a => e * (p * y a)) = fun a => e * (s • M').mulVec (fun b => e * M.mulVec y b) a := by
  change e • p • y = e • (s • M') *ᵥ (e • M *ᵥ y)
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec, smul_smul, smul_smul, smul_smul, h,
    mul_right_comm, he]

variable {D : D7} {V : HSp D}

theorem mt_one : mt V 1 = 1 := rfl

theorem mt_inv_mul (α : GA D V) : mt V α⁻¹ * mt V α = 1 := by
  rw [← GlobalTheory.SplitCentral.hmul, inv_mul_cancel, mt_one]

theorem fin_inv_mul (α : GA D V) : finMat D.sp.cm.sig V.gram (α⁻¹ : GA D V) * finMat D.sp.cm.sig V.gram α = 1 := by
  rw [GlobalTheory.SplitCentral.hfin, GlobalTheory.SplitCentral.hfin, ← Matrix.map_mul, mt_inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem fin_one : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := by
  rw [GlobalTheory.SplitCentral.hfin, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem idem_fin {e : Formalism.L2.Theta.AE D} (he : e * e = e) : finPart D e * finPart D e = finPart D e := by
  rw [← map_mul, he]

theorem int_mem (ϖ : 𝓞 D.host.E) : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, ϖ, rfl⟩

theorem hecke_one {e : Formalism.L2.Theta.AE D} (he : e * e = e) (ϖ : 𝓞 D.host.E) : IsHeckeElt V e (ϖ : D.host.E) 0 1 := by
  have hm := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  have h1 : finPart D 1 ∈ intAE D := by
    rw [map_one]; exact int_mem 1
  refine ⟨one_mem _, fun i j => ?_, fun y hy => ?_, fun y hy => ⟨_, hm _ (int_mem ϖ) y hy, ?_⟩, 1, 1, h1, h1, ?_, ?_⟩
  · rw [mt_one, sub_self, Matrix.zero_apply, mul_zero]
  · rw [fin_one, Matrix.one_mulVec]
    exact hm _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (idem_fin he)) y hy
  · rw [fin_one, Matrix.one_mulVec]
  · rw [mul_one, mul_one]
  · rw [mt_one, Matrix.det_one, pow_zero, mul_one, mul_one]

theorem hecke_compl {e s : Formalism.L2.Theta.AE D} (he : e * e = e) {ϖ : D.host.E} (hs : e * s = e * incA D ϖ) {ζ α : GA D V}
    (hζ : mt V ζ = s • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D))) {k : ℕ} (hk : k ≤ V.rank)
    (h : IsHeckeElt V e ϖ k α) (h0 : α⁻¹ * ζ ∈ GfC V) (h1 : SuppAt e V (α⁻¹ * ζ)) :
    IsHeckeElt V e ϖ (V.rank - k) (α⁻¹ * ζ) := by
  obtain ⟨-, -, h2, h3, u, u', hu, hu', h4, h5⟩ := h
  have hm := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  have hF := GlobalTheory.SplitCentral.finMat_scalar α⁻¹ ζ s hζ
  have hup : finPart D e * finPart D s = finPart D e * finPart D (incA D ϖ) := by
    rw [← RingHom.map_mul, hs, RingHom.map_mul]
  refine ⟨h0, h1, fun y hy => ?_, fun y hy => ⟨_, h2 y hy, ?_⟩, u', u, hu', hu, ?_, ?_⟩
  · obtain ⟨z, hz, hyz⟩ := h3 y hy
    rw [hF, vec_upper (fin_inv_mul α) hup hyz]
    exact hm _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (idem_fin he)) z hz
  · rw [hF]
    exact vec_lower (fin_inv_mul α) (idem_fin he) hup y
  · rw [mul_right_comm, h4]
  · have hd : (mt V α).det * (mt V α⁻¹).det = 1 := by
      rw [mul_comm, ← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
    rw [GlobalTheory.SplitCentral.hmul, hζ, Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      mul_comm (mt V α⁻¹).det]
    exact det_compl hk hs hd h4 h5

theorem exists_unif (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
  have := Ideal.pow_succ_lt_pow P.ne_bot 1
  rw [pow_one] at this
  exact SetLike.exists_of_lt this

variable {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}

theorem exists_loc (V : HSp D) (he : IsIdemAt e P) :
    ∃ S : Subgroup (GA D V), (∀ g, g ∈ S ↔ SuppAt e V g) ∧ S ≤ GfC V ∧
      ∀ g ∈ S, ∀ g', SuppF V (1 - (e + cA D e)) g' → Commute g g' := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  obtain ⟨a, b, c, -⟩ := h3 P e _ (Or.inl ⟨he, rfl⟩)
  obtain ⟨⟨L, hL⟩, -, hc⟩ := h1 _ a b
  refine ⟨L, hL, fun g hg => c g ((hL g).1 hg), fun g hg g' hg' => hc _ g g' ?_ ((hL g).1 hg) hg'⟩
  rw [mul_sub, mul_one, a, sub_self]

theorem exists_central (V : HSp D) (he : IsIdemAt e P) {ϖ : D.host.E} (hϖ : ϖ ≠ 0) :
    ∃ ζ : GA D V, (∀ g, Commute ζ g) ∧
      ∀ k ≤ V.rank, ∀ α, IsHeckeElt V e ϖ k α → IsHeckeElt V e ϖ (V.rank - k) (ζ * α⁻¹) := by
  obtain ⟨S, hS, hf, -⟩ := exists_loc V he
  obtain ⟨s, hs, hss, hse⟩ := GlobalTheory.SplitCentral.exists_unitary (cA D) (GlobalTheory.SplitCentral.cA_cA D) e (incA D ϖ)
    (incA D ϖ⁻¹) he.1.1 he.1.2.1 (by rw [← RingHom.map_mul, mul_inv_cancel₀ hϖ, RingHom.map_one])
  obtain ⟨ζ, hζ⟩ := GlobalTheory.SplitCentral.exists_mt V s hs
  have hζS : ζ ∈ S := (hS ζ).2 fun i j => by
    rw [hζ]
    exact GlobalTheory.SplitCentral.supp_scalar _ _ hss i j
  have hcom : ∀ g, Commute ζ g := fun g => by
    refine GlobalTheory.SplitCentral.hinj (ζ * g) (g * ζ) ?_
    rw [GlobalTheory.SplitCentral.hmul, GlobalTheory.SplitCentral.hmul, hζ]
    exact GlobalTheory.SplitCentral.scalar_comm _ _
  refine ⟨ζ, hcom, fun k hk α hα => ?_⟩
  have hm : α⁻¹ * ζ ∈ S := S.mul_mem (S.inv_mem ((hS α).2 hα.2.1)) hζS
  rw [(hcom _).eq]
  exact hecke_compl he.1.1 hse hζ hk hα (hf hm) ((hS _).1 hm)

theorem exists_reps {G : Type} [Group G] {J S : Subgroup G} {K : Set G} {T : G → Prop} (hS : ∀ g, g ∈ S ↔ T g)
    (hK : ∀ g, T g → (g ∈ J ↔ g ∈ K)) (hs : ∀ k ∈ J, ∃ a ∈ J, ∃ b ∈ J, T a ∧ (∀ x ∈ S, Commute x b) ∧ k = a * b)
    (hθ : ∃ θ : G → G, (∀ g, T g → T (θ g)) ∧ (∀ x y, T x → T y → θ (x * y) = θ y * θ x) ∧ (∀ x, T x → θ (θ x) = x) ∧
      (∀ k ∈ {k | k ∈ K ∧ T k}, θ k ∈ K) ∧ ∀ g, T g → ∃ a ∈ {k | k ∈ K ∧ T k}, ∃ b ∈ {k | k ∈ K ∧ T k}, θ g = a * g * b)
    (hrep : ∀ g, T g → ∃ R : Finset G, (∀ γ ∈ R, T γ) ∧
      (∀ γ ∈ R, ∃ k₁ ∈ {k | k ∈ K ∧ T k}, ∃ k₂ ∈ {k | k ∈ K ∧ T k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ T k}, ∃ k₂ ∈ {k | k ∈ K ∧ T k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ T k})
    {α : G} (hα : T α) : ∃ R R' : Finset G, IsDC J α⁻¹ R ∧ IsDC J α R' ∧ R.card = R'.card := by
  have hm : ∀ k, k ∈ {k | k ∈ K ∧ T k} ↔ k ∈ J ⊓ S := fun k => by
    rw [Subgroup.mem_inf, hS]
    exact and_congr_left fun hk => (hK k hk).symm
  simp only [hm] at hθ hrep
  simp only [← hS] at hθ hrep hα hs hK
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ := hθ
  have hdc : ∀ x ∈ S, ∃ R : Finset G, (∀ γ ∈ R, γ ∈ S) ∧ IsDC J x R := by
    intro x hx
    obtain ⟨R, h1, h2, h3⟩ := hrep x hx
    refine ⟨R, h1, isDC_of_local hx h1 (fun k hk => ?_) h2 h3⟩
    obtain ⟨a, ha, b, hb, s1, s2, e1⟩ := hs k hk
    exact ⟨a, ha, b, hb, s1, s2 x hx, e1⟩
  obtain ⟨R, hR, d1⟩ := hdc _ (S.inv_mem hα)
  obtain ⟨R', hR', d2⟩ := hdc _ hα
  have u2 : ∀ x ∈ S, ∀ y ∈ S, θ (x * y) = θ y * θ x := fun x hx y hy => t2 x y hx hy
  have u4 : ∀ k ∈ J ⊓ S, θ k ∈ J := fun k hk => (hK _ (t1 k hk.2)).2 (t4 k hk)
  exact ⟨R, R', d1, d2, le_antisymm (GlobalTheory.DoubleCosetComm.card_le_inv u2 t3 u4 t1 t5 d1 (by rwa [inv_inv]) hR)
    (GlobalTheory.DoubleCosetComm.card_le_inv u2 t3 u4 t1 t5 d2 d1 hR')⟩

theorem central_and_complement : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → ∃ z : GA D V, (∀ g, Commute z g) ∧ IsHeckeAt V PP V.rank z ∧ ∀ k ≤ V.rank, ∃ (α : GA D V) (R R' : Finset (GA D V)), IsHeckeAt V PP k α ∧ IsHeckeAt V PP (V.rank - k) (z * α⁻¹) ∧ Bridge.IsDC (levG V β L) α⁻¹ R ∧ Bridge.IsDC (levG V β L) α R' ∧ R.card = R'.card := by
  intro D V β Λ N L P hβ hN hL hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hP.1
  obtain ⟨ϖ, h1, h2⟩ := exists_unif P
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun e0 => h2 (by rw [show ϖ = 0 from Subtype.ext e0]; exact zero_mem _)
  obtain ⟨S, hS, -, hc⟩ := exists_loc V he
  obtain ⟨l1, -, l3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hβ).2 P e _ (Or.inl ⟨he, rfl⟩) hN hL
  obtain ⟨hθ, hrep, hel⟩ := GlobalTheory.T.involution_spherical_hecke_anti V P e he
  obtain ⟨ζ, hcom, hco⟩ := exists_central V he hϖ
  refine ⟨ζ, hcom, ⟨e, ϖ, he, h1, h2, ?_⟩, fun k hk => ?_⟩
  · have := hco 0 (Nat.zero_le _) 1 (hecke_one he.1.1 ϖ)
    rwa [Nat.sub_zero, inv_one, mul_one] at this
  · obtain ⟨α, hα⟩ := (hel ϖ h1 h2).1 k hk
    obtain ⟨R, R', h⟩ := exists_reps (J := levG V β L) (K := KsphC V ∅) (T := SuppAt e V) hS l1 (fun k hk => by
      obtain ⟨x, hx, y, hy, s1, s2, e1⟩ := l3 k hk
      exact ⟨x, hx, y, hy, s1, fun g hg => hc g hg y s2, e1⟩) hθ (fun g hg => by
      obtain ⟨R, r1, r2, r3⟩ := hrep g hg
      exact ⟨R, r1, fun γ hγ => (r2 γ hγ).2, r3⟩) hα.2.1
    exact ⟨α, R, R', ⟨e, ϖ, he, h1, h2, hα⟩, ⟨e, ϖ, he, h1, h2, hco k hk α hα⟩, h⟩

end GlobalTheory.HeckeCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormsDifferentialClosed
section
open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.StabD

variable {K : Type} [Field K]

theorem dK_unit (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  rw [dlog, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero, one_smul]

theorem dlog_mul (u w : Kˣ) : dlog (u * w) = dlog u + dlog w := by
  simp only [dlog, Units.val_inv_eq_inv_val, Units.val_mul, dK, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

theorem dlog_one : dlog (1 : Kˣ) = 0 := by simp [dlog]

theorem dlog_inv (u : Kˣ) : dlog u⁻¹ = -dlog u := by
  have h := dlog_mul u⁻¹ u
  rw [inv_mul_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem dlog_pow (u : Kˣ) (m : ℕ) : dlog (u ^ m) = (m : K) • dlog u := by
  induction m with
  | zero => simp [dlog_one]
  | succ m ih => rw [pow_succ, dlog_mul, ih, Nat.cast_succ, add_smul, one_smul]

theorem dlog_prod {ι : Type} (s : Finset ι) (f : ι → Kˣ) : dlog (∏ i ∈ s, f i) = ∑ i ∈ s, dlog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul, ih]

theorem dDR_dlog (u : Kˣ) : CechDR.dDR ℤ K (CechDR.ι1 (dlog u)) = 0 := by
  have hD : dK ((u⁻¹ : Kˣ) : K) = -(((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K)) • dK (u : K) := by
    rw [dK_unit, dlog_inv, dlog, smul_neg, smul_smul, neg_smul]
  rw [dlog, map_smul, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero]
  change CechDR.ι1 (dK ((u⁻¹ : Kˣ) : K)) * CechDR.ι1 (dK (u : K)) = 0
  rw [hD, map_smul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero]

theorem dDR_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    CechDR.dDR ℤ K (CechDR.ι1 (frame x J i)) = 0 := by
  unfold frame
  split_ifs
  · exact dDR_dlog _
  · exact CechDR.dDR_D _

theorem dDR_ιMulti (q : ℕ) (v : Fin q → Ω[K⁄ℤ]) (hv : ∀ i, CechDR.dDR ℤ K (CechDR.ι1 (v i)) = 0) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ιMulti K q v) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (abelian₂ K)), CechDR.dDR_algebraMap]
    simp
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, CechDR.dDR_mul]
    change _ * CechDR.dDR ℤ K _ + CechDR.dDR ℤ K (CechDR.ι1 (v 0)) * _ = 0
    rw [ih (Matrix.vecTail v) (fun i => hv _), hv 0, mul_zero, zero_mul, add_zero]

theorem dK_mem_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (T : Kˣ) (r : Fin n → ℕ)
    (hx : AlgChart A x) (hT : dlog T = ∑ j ∈ J, (r j : K) • dlog (x j)) (c : K) (hc : c * (T : K) ∈ A) :
    ∃ d : Fin n → K, (∀ i, d i * (T : K) ∈ A) ∧ dK c = ∑ i, d i • frame x J i := by
  classical
  set a := c * (T : K) with ha
  obtain ⟨cc, hcc, hDa⟩ := hx.deriv a hc
  let e : Fin n → K := fun i => if i ∈ J then cc i * (x i : K) - a * (r i : K) else cc i
  have he : ∀ i, e i ∈ A := by
    intro i
    simp only [e]
    split_ifs
    · exact sub_mem (mul_mem (hcc i) (hx.mem i)) (mul_mem hc (natCast_mem A _))
    · exact hcc i
  have hT0 : (T : K) ≠ 0 := T.ne_zero
  refine ⟨fun i => (T : K)⁻¹ * e i, fun i => ?_, ?_⟩
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hT0, one_mul]; exact he i
  have hsum : ∑ i, e i • frame x J i = dK a - a • ∑ j ∈ J, (r j : K) • dlog (x j) := by
    have hpt : ∀ i, e i • frame x J i =
        cc i • dK (x i : K) - (if i ∈ J then (a * (r i : K)) • dlog (x i) else 0) := by
      intro i
      simp only [e, frame]
      split_ifs
      · rw [sub_smul, mul_smul, ← dK_unit]
      · rw [sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← hDa, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.smul_sum]
    simp only [smul_smul]
  have hlead : dK a = c • dK (T : K) + (T : K) • dK c := Derivation.leibniz _ _ _
  have hTc : (T : K) • dK c = dK a - a • dlog T := by
    rw [hlead, dK_unit, smul_smul, ← ha]; abel
  calc dK c = (T : K)⁻¹ • ((T : K) • dK c) := by rw [smul_smul, inv_mul_cancel₀ hT0, one_smul]
    _ = _ := by
      rw [hTc, hT, ← hsum, Finset.smul_sum]
      simp only [smul_smul]

theorem dlog_twist (p : ℕ) [CharP K p] {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ)
    (r : Fin n → ℕ) : dlog (t ^ p * ∏ j ∈ J, x j ^ r j) = ∑ j ∈ J, (r j : K) • dlog (x j) := by
  rw [dlog_mul, dlog_pow, CharP.cast_eq_zero, zero_smul, zero_add, dlog_prod]
  simp only [dlog_pow]

end GlobalTheory.LogDR.StabD

open GlobalTheory.LogDR.StabD in

theorem GlobalTheory.LogDR.extD_mem_chartForms_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  intro K _ p _ _ A n x J t r hx q η hη
  unfold chartForms spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem η hη =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hη
    obtain ⟨d, hd, hDc⟩ := dK_mem_frame A x J _ r hx (dlog_twist p x J t r) c hc
    rw [extD_apply, CechDR.dDR_smul, dDR_ιMulti q v (fun i => by
      obtain ⟨k, hk⟩ := hv i; rw [← hk]; exact dDR_frame x J k), smul_zero, add_zero]
    change CechDR.ι1 (dK c) * _ ∈ _
    rw [hDc, map_sum, Finset.sum_mul]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨d i, hd i, Fin.cons (frame x J i) v, fun k => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact ⟨i, rfl⟩
      · rw [Fin.cons_succ]; exact hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply, map_smul, smul_mul_assoc]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem cm_conj_extends_of_adjoin :
    ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M]
      (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) →
      ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧
        σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  intro F M _ _ _ _ _ _ π c hadj hc hπ

  have gen : ∀ S : Subring M, (∀ x : F, algebraMap F M x ∈ S) → π ∈ S → ∀ y : M, y ∈ S := by
    intro S hS hpS y
    let A : Subalgebra F M := { S with algebraMap_mem' := hS }
    have hle : Algebra.adjoin F {π} ≤ A := Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show π ∈ A from hpS))
    rw [hadj] at hle
    exact hle (Algebra.mem_top (x := y))

  have hconj : ∀ φ : M →+* ℂ, φ π ≠ 0 ∧ (starRingEnd ℂ) (φ π) = φ ((c : M) / π) := by
    intro φ
    have hn : Complex.normSq (φ π) = (c : ℝ) := by rw [← Complex.sq_norm]; exact hπ φ
    have hne : φ π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hn
      exact hc (by exact_mod_cast hn.symm)
    refine ⟨hne, ?_⟩
    rw [map_div₀, map_ratCast, eq_div_iff hne, mul_comm, Complex.mul_conj, hn]
    norm_cast
  obtain ⟨φ₀⟩ : Nonempty (M →+* ℂ) := inferInstance
  let ψ : M →+* ℂ := (starRingEnd ℂ).comp φ₀
  have hrange : ∀ y : M, ψ y ∈ φ₀.range := by
    refine gen (Subring.comap ψ φ₀.range) ?_ ?_
    · intro x
      show ψ (algebraMap F M x) ∈ φ₀.range
      refine ⟨algebraMap F M (IsCMField.complexConj F x), ?_⟩
      exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x)
    · show ψ π ∈ φ₀.range
      exact ⟨(c : M) / π, ((hconj φ₀).2).symm⟩
  let e : M ≃+* φ₀.range := RingEquiv.ofBijective φ₀.rangeRestrict
    ⟨fun a b h => φ₀.injective (congrArg Subtype.val h), φ₀.rangeRestrict_surjective⟩
  let σ : M →+* M := e.symm.toRingHom.comp (ψ.codRestrict φ₀.range hrange)
  have hσ0 : ∀ x : M, φ₀ (σ x) = (starRingEnd ℂ) (φ₀ x) := by
    intro x
    have h1 : e (σ x) = ψ.codRestrict φ₀.range hrange x := by simp [σ]
    have h2 : ((e (σ x) : φ₀.range) : ℂ) = ((ψ.codRestrict φ₀.range hrange x : φ₀.range) : ℂ) := congrArg Subtype.val h1
    exact h2
  have hσF : ∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x) := by
    intro x
    apply φ₀.injective
    rw [hσ0]
    exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x).symm
  have hσπ : σ π = (c : M) / π := by
    apply φ₀.injective
    rw [hσ0]; exact (hconj φ₀).2
  have hπ0 : π ≠ 0 := fun h => (hconj φ₀).1 (by rw [h, map_zero])
  refine ⟨σ, hσF, ?_, ?_⟩
  · rw [hσπ, div_mul_cancel₀ _ hπ0]
  · intro φ
    have := gen (RingHom.eqLocus (φ.comp σ) ((starRingEnd ℂ).comp φ)) ?_ ?_
    · intro x; exact this x
    · intro x
      show φ (σ (algebraMap F M x)) = (starRingEnd ℂ) (φ (algebraMap F M x))
      rw [hσF]
      exact IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F M)) x
    · show φ (σ π) = (starRingEnd ℂ) (φ π)
      rw [hσπ]; exact ((hconj φ).2).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibrationStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_normal_subgroup_fibration : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  first | exact @GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo | exact GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo | (intros; apply GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsBoundedRootsUnity
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit

open Matrix

theorem vandermonde_integral_of_roots_of_unity : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ), ¬ p ∣ N → ∀ (w : Fin r → PadicAlgCl p), (∀ s, w s ^ N = 1) → Function.Injective w → ∀ (c : Fin r → PadicAlgCl p), (∀ s, ‖∑ j : Fin r, c j * w s ^ (j : ℕ)‖ ≤ 1) → ∀ j, ‖c j‖ ≤ 1 := by
  intro p _ N r hN w hw hinj c hc j
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero p)
  have hw1 : ∀ s, ‖w s‖ = 1 := fun s => by
    have h := congrArg norm (hw s)
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 h
  set S := Obar p
  let ws : Fin r → S := fun s => ⟨w s, mem_Obar_iff.2 (hw1 s).le⟩
  let ys : Fin r → S := fun s => ⟨∑ j : Fin r, c j * w s ^ (j : ℕ), mem_Obar_iff.2 (hc s)⟩
  let V' : Matrix (Fin r) (Fin r) S := Matrix.vandermonde ws
  have hmap : V'.map S.subtype = Matrix.vandermonde w := by
    ext s t; simp [V', ws, Matrix.vandermonde_apply]
  have hdet : ‖(Matrix.vandermonde w).det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    refine Finset.prod_eq_one fun k hk => ?_
    have hik : i < k := Finset.mem_Ioi.1 hk
    exact norm_sub_eq_one_of_pow_eq_one p hN (hw k) (hw i) (fun h => (ne_of_lt hik) (hinj h).symm)
  have hdetS : (S.subtype V'.det) = (Matrix.vandermonde w).det := by
    rw [RingHom.map_det, ← hmap]; rfl
  have hne : (Matrix.vandermonde w).det ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit V'.det := by
    have hmem : ((Matrix.vandermonde w).det)⁻¹ ∈ S := by
      rw [mem_Obar_iff, norm_inv, hdet, inv_one]
    refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ ?_
    apply Subtype.ext
    change S.subtype V'.det * _ = 1
    rw [hdetS, mul_inv_cancel₀ hne]
  let c' : Fin r → S := V'⁻¹ *ᵥ ys
  have hc' : V' *ᵥ c' = ys := by
    simp only [c', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hV : Matrix.vandermonde w *ᵥ (fun k => (c' k : PadicAlgCl p)) = Matrix.vandermonde w *ᵥ c := by
    funext s
    have h1 := RingHom.map_mulVec S.subtype V' c' s
    rw [hc', hmap] at h1
    change _ = (vandermonde w *ᵥ ⇑S.subtype ∘ c') s at h1
    rw [show (fun k => (c' k : PadicAlgCl p)) = ⇑S.subtype ∘ c' from rfl, ← h1]
    simp only [ys, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    simp [mul_comm]
  have hVu : IsUnit (Matrix.vandermonde w) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have hcc : (fun k => (c' k : PadicAlgCl p)) = c := by
    have := congrArg (fun v => (Matrix.vandermonde w)⁻¹ *ᵥ v) hV
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hVu), Matrix.one_mulVec] using this
  rw [← congrFun hcc j]
  exact mem_Obar_iff.1 (c' j).2

end GlobalTheory.LKRes.ResSplit
end

