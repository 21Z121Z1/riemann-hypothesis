import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.RestGramW
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.GramInvIntV
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentOfIntegralModels
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016

-- bundled from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
section
open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp Formalism.MainNotions.G.LatticeSystems

theorem colSpan_mul_le {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} (X U : Matrix (Fin k) (Fin k) Kf)
    (hU : ∀ a b, U a b ∈ Set.range (algebraMap O Kf)) : colSpan O (X * U) ≤ colSpan O X := by
  unfold colSpan
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  choose u hu using hU
  have h : (fun i => (X * U) i c) = ∑ b, u b c • (fun i => X i b) := by
    funext i
    rw [Finset.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, hu, mul_comm]
  have hmem : (∑ b, u b c • (fun i => X i b)) ∈ Submodule.span O (Set.range fun c : Fin k => fun i => X i c) :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  rw [← h] at hmem
  exact hmem

theorem colSpan_mul_unit {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} (X U U' : Matrix (Fin k) (Fin k) Kf)
    (hU : ∀ a b, U a b ∈ Set.range (algebraMap O Kf)) (hU' : ∀ a b, U' a b ∈ Set.range (algebraMap O Kf)) (h : U * U' = 1) :
    colSpan O (X * U) = colSpan O X := by
  refine le_antisymm (colSpan_mul_le X U hU) ?_
  have := colSpan_mul_le (O := O) (X * U) U' hU'
  rwa [Matrix.mul_assoc, h, Matrix.mul_one] at this

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}

def rho (G : GAtP p) (v : Fin G.P.nV) (s : ℕ) : G.P.Qq v →+* G.Kf :=
  (G.P.ι v).comp ((G.P.σ v ^ s : G.P.Qq v ≃+* G.P.Qq v) : G.P.Qq v →+* G.P.Qq v)

theorem rho_int (v : Fin G.P.nV) (s : ℕ) (x : G.P.Qq v) (hx : x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v))) :
    rho G v s x ∈ Set.range (algebraMap G.O G.Kf) := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := la_sigma_pow (G.P.σ v) (la_frob G v) s y
  refine ⟨G.P.j v z, ?_⟩
  show _ = G.P.ι v ((G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) y))
  rw [hz, (G.P.setting v).ι_comp]

theorem latO_of (tE : Tau → E →+* LL)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hσσ : ∀ x, σ (σ x) = x)
    (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (B' : GL (Fin n) E)
    (L : G.P.Tup)
    (hL : ∀ v, L v = colSpan (G.P.W v) (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) (A.B⁻¹ * γ * B')) :
      GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hG : ∀ v a b, A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1) a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹ a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)))
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    extO G.O (G.P.ι v) (G.P.σ v) s.val (L v) =
      colSpan G.O ((nAt G.P A.rk pos (fun τ => bc (tE τ) (A.B⁻¹ * γ * B')) v s).map e) := by
  rw [hL v, la_extO_G]
  set N : GL (Fin n) E := A.B⁻¹ * γ * B' with hN
  have hX : la_tw (G.P.ι v) (G.P.σ v) s.val (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) N) :
      GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) =
      (N.1.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk) := by
    ext a b; rfl
  rw [hX]
  unfold nAt
  by_cases hs : Even s.val
  · rw [if_pos hs]
    congr 1
    ext a b
    have := hpos v s (N.1 (finCongr A.rk a) (finCongr A.rk b))
    rw [if_pos hs] at this
    exact this.symm
  · rw [if_neg hs]
    set Gm := cT (σ : E →+* E) B'.1 * J * B'.1 with hGm
    have hJ : J = cT (σ : E →+* E) (A.B⁻¹).1 * (A.B⁻¹).1 := by
      have h0 : cT (σ : E →+* E) (A.B⁻¹).1 * (cT (σ : E →+* E) A.B.1 * J * A.B.1) * (A.B⁻¹).1 = J := by
        have e1 : cT (σ : E →+* E) (A.B⁻¹).1 * cT (σ : E →+* E) A.B.1 = 1 := by
          rw [← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]
        have e2 : A.B.1 * (A.B⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        calc cT (σ : E →+* E) (A.B⁻¹).1 * (cT (σ : E →+* E) A.B.1 * J * A.B.1) * (A.B⁻¹).1
            = (cT (σ : E →+* E) (A.B⁻¹).1 * cT (σ : E →+* E) A.B.1) * J * (A.B.1 * (A.B⁻¹).1) := by
              simp only [Matrix.mul_assoc]
          _ = J := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      rw [hBs, Matrix.mul_one] at h0
      exact h0.symm
    have h1 : cT (σ : E →+* E) N.1 * N.1 = Gm := by
      have hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
      have eN : N.1 = (A.B⁻¹).1 * γ.1 * B'.1 := rfl
      rw [eN, cT_mul, cT_mul]
      calc cT (σ : E →+* E) B'.1 * (cT (σ : E →+* E) γ.1 * cT (σ : E →+* E) (A.B⁻¹).1) * ((A.B⁻¹).1 * γ.1 * B'.1)
          = cT (σ : E →+* E) B'.1 * (cT (σ : E →+* E) γ.1 * (cT (σ : E →+* E) (A.B⁻¹).1 * (A.B⁻¹).1) * γ.1) * B'.1 := by
            simp only [Matrix.mul_assoc]
        _ = Gm := by rw [← hJ, hγ']
    have h2 : cT (σ : E →+* E) (N⁻¹).1 * Gm = N.1 := by
      rw [← h1, ← Matrix.mul_assoc, ← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul]
    have hdet : IsUnit Gm.det := by
      have h3 : IsUnit (cT (σ : E →+* E) (N⁻¹).1 * Gm).det := by
        rw [h2]; exact (Matrix.isUnit_iff_isUnit_det _).1 N.isUnit
      rw [Matrix.det_mul] at h3
      exact isUnit_of_mul_isUnit_right h3
    have h3 : cT (σ : E →+* E) (N⁻¹).1 = N.1 * Gm⁻¹ := by
      rw [← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    have hY : ((((bc (tE (pos ⟨v, s⟩)) N)⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr A.rk)
        (finCongr A.rk)).map e =
        ((N.1 * Gm⁻¹).map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk) := by
      rw [← map_inv, ← h3]
      ext a b
      have h4 := hpos v s ((cT (σ : E →+* E) (N⁻¹).1) (finCongr A.rk a) (finCongr A.rk b))
      rw [if_neg hs] at h4
      have h5 : σ ((cT (σ : E →+* E) (N⁻¹).1) (finCongr A.rk a) (finCongr A.rk b)) =
          (N⁻¹).1 (finCongr A.rk b) (finCongr A.rk a) := hσσ _
      rw [h5] at h4
      exact h4
    rw [hY, Matrix.map_mul, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr A.rk) _]
    refine (colSpan_mul_unit ((N.1.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk))
      ((Gm⁻¹.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk))
      ((Gm.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk))
      (fun a b => rho_int v s.val _ (hG v _ _).2) (fun a b => rho_int v s.val _ (hG v _ _).1) ?_).symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

set_option maxHeartbeats 4000000 in
theorem restLatO_of {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}
    (hpos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
      I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
        (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x)))
    (h1 : RestLatW T I) (h2 : RestGramW I) : RestLatO T Gt I := by
  intro u w hg i L c g γ κ hg' hγ hpt B' hB' v s
  exact latO_of (tEL D) (hpos u w hg) (fun x => by rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive]) (locAt_std u w hg I.B I.B_std) γ hγ B' L
    (h1 u w hg i L c g γ κ hg' hγ hpt B' hB') (h2 u w hg c B' hB') v s

theorem span_dualSet {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) :
    ((Submodule.span (𝓞 K) (dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = dualSet σ J L := by
  apply le_antisymm
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero =>
      intro x _
      refine ⟨0, ?_⟩
      simp [Formalism.UG.hform]
    | add y y' _ _ hy hy' =>
      intro x hx
      have e : Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
        simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem (hy x hx) (hy' x hx)
    | smul r y _ hy =>
      intro x hx
      have e : Formalism.UG.hform σ J x (r • y) = algebraMap (𝓞 K) K r * Formalism.UG.hform σ J x y := by
        simp only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact mul_mem ⟨r, rfl⟩ (hy x hx)
  · exact Submodule.subset_span

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB in
theorem restExB (D : D7) : RestExB D := by
  intro u w _ c
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hL := bwB_clsCrd_lat D u 0 (Nat.zero_le _) c
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (bwB_gramN_det D 0 (Nat.zero_le _)) _ hL
  have hLd : Ld D u 0 (Nat.zero_le _) c ≤ bnd d := hle
  have hLd_sp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) _ hL
  obtain ⟨B, hB⟩ := exists_isLocBasis (D.what₂.places.resChar w) _ _ (fg_of_le_bnd hd hLd) hLd_sp
  refine ⟨B, ?_⟩
  have e : (Ld D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c) := span_dualSet _ _ _
  rwa [e] at hB

def unitsW (D : D7) (w : D.what₂.places.Pl) : Submonoid ℂ where
  carrier := {z | ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = z}
  one_mem' := ⟨1, one_mem _, by rw [inv_one]; exact one_mem _, map_one _⟩
  mul_mem' := by
    rintro _ _ ⟨r, hr, hr', rfl⟩ ⟨s, hs, hs', rfl⟩
    exact ⟨r * s, mul_mem hr hs, by rw [mul_inv]; exact mul_mem hr' hs', map_mul _ _ _⟩

theorem unitsW_inv {w : D.what₂.places.Pl} {z : ℂ} (h : z ∈ unitsW D w) : z⁻¹ ∈ unitsW D w := by
  obtain ⟨r, hr, hr', rfl⟩ := h
  exact ⟨r⁻¹, hr', by rwa [inv_inv], map_inv₀ _ _⟩

theorem unitsW_of_pow {w : D.what₂.places.Pl} {r : D.what₂.LL} {N : ℕ} (hN : 0 < N) (h : r ^ N = 1) :
    D.what₂.embLL r ∈ unitsW D w := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at h
    exact zero_ne_one h
  have hr : r ∈ intW D.what₂.places w := by
    have htop : D.what₂.places.val w r ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact hr0
    obtain ⟨a, ha⟩ : ∃ a : ℤ, D.what₂.places.val w r = (a : WithTop ℤ) := ⟨_, (WithTop.coe_untop _ htop).symm⟩
    have h1 : N • D.what₂.places.val w r = 0 := by rw [← AddValuation.map_pow, h, AddValuation.map_one]
    rw [ha, ← WithTop.coe_nsmul, WithTop.coe_eq_zero] at h1
    have ha0 : a = 0 := by
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hN.ne'
      · exact h2
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w r
    rw [ha, ha0]
    exact le_refl _
  have hinv : r⁻¹ = r ^ (N - 1) := (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hN.ne', h])).symm
  exact ⟨r, hr, by rw [hinv]; exact pow_mem hr _, rfl⟩

set_option maxHeartbeats 1000000 in
theorem restChi_of (T : ∀ u : D.what₂.Word, Forms0 D u) (h : ∀ u, LevelZeroCharacterRational T u) : RestChi T := by
  intro u w _ κ
  have key : ((((T u).cls0).lev.chi κ : ℂˣ) : ℂ) ∈ unitsW D w := by
    rw [((T u).glev0).chi_eq κ]
    refine prod_mem fun i _ => ?_
    refine finprod_induction (fun z : ℂ => z ∈ unitsW D w) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
    refine finprod_induction (fun z : ℂ => z ∈ unitsW D w) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_
    refine unitsW_inv ?_
    unfold lamJ
    rw [Finset.range_zero, Finset.prod_empty, mul_one]
    suffices hall : ∀ t : kv D.host.F v, (T u).gl.psi0 i v hv t ∈ unitsW D w from hall _
    intro t
    obtain ⟨r, hr⟩ := h u i v hv t
    rw [← hr]
    refine unitsW_of_pow (N := D.host.g i) (D.host.g_prime i).pos ?_
    apply D.what₂.embLL.injective
    have h0 : ((D.host.g i : ℕ) : kv D.host.F v) = 0 := by
      have h1 : algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) (D.host.g i : 𝓞 D.host.F) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers D.host.F) := (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.mem_maximal_ideal_completion_iff v _).2 hv
      have h2 := (IsLocalRing.residue_eq_zero_iff _).2 h1
      rw [map_natCast, map_natCast] at h2
      exact h2
    rw [map_pow, map_one, hr, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, h0, zero_mul, AddChar.map_zero_eq_one]
  obtain ⟨r, hr, hr', e⟩ := key
  exact ⟨r, hr, hr', e⟩

end Formalism.L2.G.RelativeIndexFlags
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
section
noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.G.Cmp
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem selfDual_congr (v : HeightOneSpectrum (𝓞 F)) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (h : latS (F := F) (v.adicCompletion F) (intV E v) L = latS (F := F) (v.adicCompletion F) (intV E v) L')
    (hs : SelfDualAt σ J v L) : SelfDualAt σ J v L' := by
  intro y
  have h1 : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) L' ↔
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := fun z => by rw [h]
  exact (h1 y).trans ((hs y).trans ⟨fun H z hz => H z ((h1 z).1 hz), fun H z hz => H z ((h1 z).2 hz)⟩)

theorem loc_facts (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (hT : ¬ p ∣ T) (Lc : Submodule (𝓞 E) (Fin n → E))
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B') :
    SelfDualAt σ J v (latB B') ∧ ∀ (κ : S.U) (x : Fin n → E ⊗[F] v.adicCompletion F),
      x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latB B') ↔
        (((bc (prV (E := E) v) (y.1 * κ.1))⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  have hsdb : SelfDualAt σ J v S.Lb := self_dual_lattice_at F E n σ J v S.Lb T S.Lb_fin
    (fun x hx y hy => S.Lb_int y hy x hx) (fun y hy => S.Lb_dual y hy) (natCast_notMem v hp hv hT)
  have hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lc ↔
      (((bc (prV (E := E) v) y.1)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    intro x
    rw [← map_inv]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hy x
  have hsdc : SelfDualAt σ J v Lc := selfDual_move v (bc (prV (E := E) v) y.1) (Formalism.UG.P.afsplit_bc_mem σ J v _ y.2) hyl hsdb
  have hLd : ((dualL (σ : E →+* E) J Lc : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = dualSet (σ : E →+* E) J Lc :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_span_dualSet _ _ _
  have e1 := latS_dual_eq v hLd (fun x hx => Submodule.subset_span (hle x hx)) hsdc
  have e2 := latS_of_locBasis v hp hv (dualL (σ : E →+* E) J Lc) B' (by rw [hLd]; exact hB')
  have e : latS (F := F) (v.adicCompletion F) (intV E v) Lc = latS (F := F) (v.adicCompletion F) (intV E v) (latB B') :=
    e1.symm.trans e2
  refine ⟨selfDual_congr v e hsdc, fun κ x => ?_⟩
  have hκ : bc (prV (E := E) v) κ.1 ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) :=
    (S.Uloc_lev v (((S.U_eq κ.1).1 κ.2).2 v)).2
  have hκ' := (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hκ
  rw [← e, hyl x, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact hκ' _

variable {p : ℕ} {G : GAtP p}

theorem latW_gen (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U)
    (hpt : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 * κ.1)) (v : Fin G.P.nV) :
    colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) =
      colSpan (G.P.W v) (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) (A.B⁻¹ * γ * B')) : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
        Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  obtain ⟨h1, h2⟩ := int_of_move (A.pl v).1 (A.spl v) (halg v) A.B B' (hb v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ.1))
    ((loc_facts S (A.pl v).1 hp (A.pl v).2 hT Lc y hy hle B' hB').2 κ)
  exact lat_of_int A hW i g γ B' (y.1 * κ.1) (by rw [← mul_assoc]; exact hpt) v h1 h2

theorem gramW_gen (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a)) (hJ : IsUnit J.det)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B') (v : Fin G.P.nV) (a b : Fin n) :
    A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1) a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹ a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  have hsd := (loc_facts S (A.pl v).1 hp (A.pl v).2 hT Lc y hy hle B' hB').1
  have hG : IsUnit (cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E)).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    refine (IsUnit.mul ?_ hJ).mul ((Matrix.isUnit_iff_isUnit_det _).1 B'.isUnit)
    have h0 := (Matrix.isUnit_iff_isUnit_det _).1 (bc (σ : E →+* E) B').isUnit
    show IsUnit (((bc (σ : E →+* E) B' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᵀ).det
    rw [Matrix.det_transpose]
    exact h0
  have key : ∀ x : E, inclE (F := F) ((A.pl v).1.adicCompletion F) x ∈ intV E (A.pl v).1 →
      A.iw v x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
    intro x hx
    refine (hW v _).2 ?_
    have e : A.eQ v (A.iw v x) = (A.spl v (inclE (F := F) ((A.pl v).1.adicCompletion F) x)).1 :=
      (A.eQ v).apply_symm_apply _
    rw [e]
    exact Formalism.MainNotions.Gaps.Loc.fst_int (A.pl v).1 (A.spl v) (halg v) _ hx
  exact ⟨key _ (gram_intV (A.pl v).1 B' hsd a b), key _ (gramInv_intV (A.pl v).1 B' hsd hG a b)⟩

theorem frlat_re {k : ℕ} (hk : k = n) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb0 : Submodule (𝓞 E) (Fin k → E)) (B0 : GL (Fin k) E) (fr : GL (Fin k) (v.adicCompletion F))
    (hfr : fr = bc (piE v φ) B0)
    (h : ∀ t : Fin k → v.adicCompletion F, (∃ x ∈ Formalism.L2.Herm.locL v Lb0, ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, ((fr⁻¹ : GL (Fin k) (v.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F)
    (Lb' : Submodule (𝓞 E) (Fin n → E)) (hLb : Lb' = reL hk Lb0) :
    ∀ t : Fin n → v.adicCompletion F, (∃ x ∈ Formalism.L2.Herm.locL v Lb', ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (piE v φ) (reGL hk E B0))⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F := by
  subst hk
  subst hfr
  subst hLb
  have e1 : reL (rfl : k = k) Lb0 = Lb0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [e1, reGL_rfl]
  exact h

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

set_option maxHeartbeats 4000000 in

theorem hb_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) (hJ : ∀ u, Joint0 X.lev0 u (T u)) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV)
    (t : Fin (D.R.N 0) → ((locAt X u w hg I.B).pl v).1.adicCompletion D.host.F) :
    (∃ x ∈ Formalism.L2.Herm.locL ((locAt X u w hg I.B).pl v).1 ((T u).cls0).lev.Lb,
        ∀ a, ((locAt X u w hg I.B).spl v (x a)).1 = t a) ↔
      ∀ a, (((bc ((locAt X u w hg I.B).phE v) (locAt X u w hg I.B).B)⁻¹ :
        GL (Fin (D.R.N 0)) (((locAt X u w hg I.B).pl v).1.adicCompletion D.host.F)) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _).mulVec t a ∈
          ((locAt X u w hg I.B).pl v).1.adicCompletionIntegers D.host.F := by
  exact frlat_re (rank_eq_first_level D.R) ((X.g u w hg).pl v).1 ((X.g u w hg).spl _ ((X.g u w hg).pl v).2) (X.lev0 u).Lb I.B
    ((X.g u w hg).fr _ ((X.g u w hg).pl v).2) (I.fr_B u w hg _ ((X.g u w hg).pl v).2)
    ((X.g u w hg).fr_lat _ ((X.g u w hg).pl v).2) ((T u).cls0).lev.Lb (hJ u).Lb_eq t

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem lcInt_of_cls {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c ≤ Ld D u i hi c := by
  intro x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
    intro z hz
    exact (K.y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ K.lev.Lb, ∀ b ∈ K.lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := K.lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) K.lev.Lb 1 hm (K.y c).1
    (K.y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwL_descent _ _ _ h

set_option maxHeartbeats 4000000 in
theorem hle_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    ∀ x ∈ clsCrd D u 0 (Nat.zero_le _) c,
      x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c) := by
  intro x hx
  have h := lcInt_of_cls (T u).cls0 c hx
  rw [← SetLike.mem_coe, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_Ld_coe] at h
  exact h

set_option maxHeartbeats 8000000 in

theorem restLatW_of (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) (hJ : ∀ u, Joint0 X.lev0 u (T u)) :
    RestLatW T I := by
  intro u w hg i L c g γ κ hL _ hpt B' hB' v
  rw [hL v]
  exact latW_gen ((T u).cls0).lev (locAt X u w hg I.B) (locInt_locAt X u w hg I.B) hg.1 hg.2.2.2.2.2
    (fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a) (hb_rec T I hJ u w hg)
    (clsCrd D u 0 (Nat.zero_le _) c) (((T u).cls0).y c) (((T u).cls0).y_lat c)
    (hle_rec T u c) B' hB' i g γ κ hpt v

set_option maxHeartbeats 8000000 in

theorem restGramW_of (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) : RestGramW I := by
  intro u w hg c B' hB' v a b
  exact gramW_gen ((T u).cls0).lev (locAt X u w hg I.B) (locInt_locAt X u w hg I.B) hg.1 hg.2.2.2.2.2
    (fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _))
    (clsCrd D u 0 (Nat.zero_le _) c) (((T u).cls0).y c) (((T u).cls0).y_lat c)
    (hle_rec T u c) B' hB' v a b

end Formalism.L2.G.RelativeIndexFlags
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
section
namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

theorem oddFact_pf {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    OddFact (K := K) O m lam := oddDualWeyl O m lam

theorem weylLatticeDescent_holds : WeylLatticeDescent := weylLatticeDescent_of_integral_models fun m lam _ => oddFact_pf ℤ m lam

end Formalism.L2.G.RelativeIndexFlags
end

