import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0016
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVN

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fixF (K : Type) [Field K] [NumberField K] [StarRing K] :
    ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap (cmF K) K) := by
  intro a
  constructor
  · intro h
    exact ⟨⟨a, (mem_cmF_iff K a).2 h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact star_coe_cmF K x

theorem card_quot (hK : IsCMUnram K) :
    Nat.card ((𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range) = 2 ^ fDeg K := by
  rw [Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex (cmF K) (isReal_cmF hK),
    (discrTower K (cmF K) hK (fixF K)).2.1]

theorem span_mul_span1 (x y : K) :
    Submodule.span (𝓞 K) {x} * Submodule.span (𝓞 K) {y} = Submodule.span (𝓞 K) {x * y} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem iota_inv (x : (𝓞 (cmF K))ˣ) : iota K x⁻¹ = (iota K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

theorem iota_ne_zero (x : (𝓞 (cmF K))ˣ) : iota K x ≠ 0 := by
  intro h0
  have := congrArg (iota K) (mul_inv_cancel x)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

theorem star_iota (x : (𝓞 (cmF K))ˣ) : star (iota K x) = iota K x := star_coe_cmF K _

theorem card_classReps_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0)
    (s : Finset (Submodule (𝓞 K) K)) (hs : IsClassReps h (1 : Submodule (𝓞 K) K) s) :
    s.card ≤ classNumber K * 2 ^ fDeg K := by
  classical
  have hlat : ∀ M : s, Submodule.IsLattice K (M : Submodule (𝓞 K) K) := fun M => (hs.1 M M.2).1
  let cl : s → ClassGroup (𝓞 K) := fun M => ClassGroup.mk K (fracU (hlat M))
  let base : s → s := fun M => Classical.choose (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have hbase : ∀ M, cl (base M) = cl M := fun M =>
    Classical.choose_spec (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have gen : ∀ (γ γ' : ClassGroup (𝓞 K)) (hγ : ∃ B : s, cl B = γ) (hγ' : ∃ B : s, cl B = γ'),
      γ = γ' → Classical.choose hγ = Classical.choose hγ' := by
    intro γ γ' hγ hγ' e
    subst e
    rfl
  have hbase_eq : ∀ M M', cl M = cl M' → base M = base M' := fun M M' e => gen _ _ _ _ e
  have hex : ∀ M : s, ∃ a : K, a ≠ 0 ∧
      (M : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) {a} * ((base M : s) : Submodule (𝓞 K) K) :=
    fun M => exists_eq_span_mul (hlat M) (hlat (base M)) (hbase M).symm
  choose a ha0 haM using hex
  have hu : ∀ M : s, ∃ t : (𝓞 (cmF K))ˣ, iota K t = a M * star (a M) := by
    intro M
    obtain ⟨i1, i2⟩ := norm_unit h h1 (hs.1 M M.2) (hs.1 _ (base M).2) (haM M)
    exact exists_unitF (mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))) i1 i2
      (by rw [star_mul', star_star, mul_comm])
  choose t ht using hu
  let Q := (𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range
  let Ψ : s → ClassGroup (𝓞 K) × Q := fun M => (cl M, ((t M : (𝓞 (cmF K))ˣ) : Q))
  have hinj : Function.Injective Ψ := by
    intro M M' e
    have ecl : cl M = cl M' := congrArg Prod.fst e
    have eB : base M = base M' := hbase_eq M M' ecl
    have eq : ((t M : (𝓞 (cmF K))ˣ) : Q) = ((t M' : (𝓞 (cmF K))ˣ) : Q) := congrArg Prod.snd e
    rw [QuotientGroup.eq] at eq
    obtain ⟨v, hv⟩ := eq
    set ν : K := iota K v with hνdef
    have hν0 : ν ≠ 0 := iota_ne_zero v
    have hνs : star ν = ν := star_iota v
    have hv' : ν ^ 2 = (iota K (t M))⁻¹ * iota K (t M') := by
      rw [hνdef, ← map_pow, ← iota_inv, ← map_mul, ← hv, powMonoidHom_apply]
    have hu0 : a M * star (a M) ≠ 0 := mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))
    have key : a M' * star (a M') = a M * star (a M) * ν ^ 2 := by
      rw [← ht M, ← ht M', hv', mul_inv_cancel_left₀ (iota_ne_zero _)]
    set b : K := a M' * (a M * ν)⁻¹ with hbdef
    have hb0 : b ≠ 0 := mul_ne_zero (ha0 M') (inv_ne_zero (mul_ne_zero (ha0 M) hν0))
    have hb : star b * b = 1 := by
      have e : star b * b = (a M' * star (a M')) * (a M * star (a M) * ν ^ 2)⁻¹ := by
        rw [hbdef, star_mul', star_inv₀, star_mul', hνs]
        have hsa : star (a M) ≠ 0 := star_ne_zero.2 (ha0 M)
        field_simp
      rw [e, key, mul_inv_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hν0))]
    let g : K ≃ₗ[K] K := LinearEquiv.smulOfNeZero K K b hb0
    have hg : g ∈ isom h := by
      refine (mem_isom_iff h1 g).2 ?_
      show star (b • (1 : K)) * (b • (1 : K)) = 1
      rw [smul_eq_mul, mul_one]
      exact hb
    obtain ⟨w, hw⟩ := exists_unitK v
    have hwinv : algebraMap (𝓞 K) K ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ν⁻¹ := by
      rw [hνdef, ← hw]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    have hgM : gmap g (M : Submodule (𝓞 K) K) = M' := by
      rw [gmap_smul, haM M, haM M', ← eB, ← mul_assoc, span_mul_span1]
      have e : b * a M = a M' * ν⁻¹ := by
        rw [hbdef]
        field_simp
        exact mul_div_cancel_right₀ _ (ha0 M)
      rw [e, ← span_mul_span1, mul_assoc, ← hwinv, span_unit_mul]
    have hU := hs.2 M' (hs.1 M' M'.2)
    exact Subtype.ext (hU.unique ⟨M.2, g, hg, hgM⟩ ⟨M'.2, 1, (isom h).one_mem, gmap_one _⟩)
  have hQ : Nat.card Q = 2 ^ fDeg K := card_quot hK
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  have hc := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, hQ, Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K)), Nat.card_eq_fintype_card,
    Fintype.card_coe] at hc
  exact hc

theorem mass_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) :
    mass h (1 : Submodule (𝓞 K) K) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  unfold mass
  split_ifs with hex
  · refine le_trans ?_ (Nat.cast_le.2 (card_classReps_le hK h h1 _ hex.choose_spec))
    calc ∑ M ∈ hex.choose, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ _M ∈ hex.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (autL h M)) with h0 | hpos
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
      _ = (hex.choose.card : ℝ) := by simp
  · positivity

theorem isLattice_one : Submodule.IsLattice K (1 : Submodule (𝓞 K) K) :=
  ⟨⟨{1}, by rw [Finset.coe_singleton, ← Submodule.one_eq_span]⟩,
    span_eq_top_of_ne_zero (Submodule.mem_one.2 ⟨1, map_one _⟩) one_ne_zero⟩

theorem mass_std_one_le (hK : IsCMUnram K) :
    mass (stdForm K 1) (stdLat K 1) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  have hs := stdForm_isSymm K 1
  have ho := stdLat_isOrtho K 1
  have := finiteDimensional_of_ortho ho
  obtain ⟨h', A, hn, hA, hex, e⟩ := exists_model hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isLattice_of_ortho ho)
  rw [← e, ← mass_eq_of_lattices hn hn hA isLattice_one hex]
  exact mass_le hK h' hn

end Formalism.MainNotions.BridgeLemVN

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
section
noncomputable section

namespace Formalism.MainNotions.OnePlaceExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds

section OnePl

variable (D : D7)

def PlaceOK (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D) ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec ∧
    Tz D.R.k D.R.rS L.z = T ∧ Tz D.R.k D.R.rS L.z' = T'

def BpReal (Ch Cg dist : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK D Ch Cg T T' b dist v L f μsec →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ →
      ENNReal.ofReal (nLoc D T T' v γ) * orbSq L f (Pv.Frames.turnPt (ptLoc D v γ)) ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) *
          jNorm2 L f μsec

def QExpAt (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (dist' : ℝ) (A : ℕ) (C : ℝ)
    (e : ℕ) (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ∃ (n : ℕ) (a : Fin n → ℝ) (L' : Fin n → LocBessel D.R.k D.R.rS)
      (f' : ∀ i, Mx D.R.k D.R.rS → ((L' i).Wq →L[ℂ] (L' i).Wp))
      (μ' : Fin n → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ),
      (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) ∧
      (∀ i, PlaceOK D Ch Cg T T' b dist' v (L' i) (f' i) (μ' i)) ∧
      (∀ i, jNorm2 (L' i) (f' i) (μ' i) ≤ jNorm2 (X.L v) (X.f v) (X.μsec v)) ∧
      ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
          orbSq (X.L v) (X.f v) (Pv.Frames.turnPt (ptLoc D v γ)) ≤
        (∑ i, ENNReal.ofReal (a i) *
          (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (Pv.Frames.turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2)) ^ 2

variable {D}

end OnePl

section ThmB

variable {D : D7}

end ThmB

def TieTop : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (ν' : Fin (2 * r + (k0 + 1) + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r),
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
    ∃ c : List ℕ → ℝ, (∀ s, 0 < c s) ∧
      ∀ (F : Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (Formalism.MainNotions.BigCellDensity.A0 (k0 + 1) r) 1 F →
        0 < Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        orbSq L F γ = ENNReal.ofReal (c (γ.1.map Prod.snd) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re)

section Frames

open Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.OnePlaceEstimates in

theorem frame_bound_of_bessel_torus (D : D7) (Cgf Cf : ℝ) (hCf : 2 ≤ Cf) (hOB : OneBesselTor D Cgf) :
    Formalism.MainNotions.OnePlaceEstimates.FrameBesselBound D Cgf Cf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨f₁, C, hC, hf₁, hJ, hO⟩ := hOB L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have e1 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z = τ ^ 2 * Tz D.R.k D.R.rS L.z := Tz_smul _ _
  have e2 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z' = τ ^ 2 * Tz D.R.k D.R.rS L.z' := Tz_smul _ _
  refine ⟨trDat L κ τ hκ hτ, f₁, rfl, rfl, rfl, rfl, ?_, ?_, ?_, e1, e2, hf₁, ?_⟩
  · show (κ : ℂ) * L.c = _
    rw [hc]; unfold cOfDpsi; push_cast; ring
  · show 0 < L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ)
    exact ENNReal.mul_pos hκN.ne' (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  · show L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ) ≠ ⊤
    exact ENNReal.mul_ne_top hκNt ENNReal.ofReal_ne_top
  intro μsec hsec
  refine ⟨secTr τ μsec, isSection_tr hτ hsec, jacBig D.R.rS κ τ * wBig D.R.k D.R.rS κ τ * ‖C‖ ^ 2,
    mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2), ?_, ?_⟩
  · refine jNorm2_tr hκ hτ L (trDat L κ τ hκ hτ) e1 e2 f f₁ μsec (secTr τ μsec) C hk2 fun p hp hζ => ?_
    rw [secTr_sBig hτ]
    have hb : bigCell D.R.k D.R.rS (sBig D.R.rS κ τ p).1 (μsec p.2) =
        cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)) := by
      rw [bigCell_cj hκ hτ]; rfl
    rw [hb]
    show @hsNormSq L.Wp L.Wq _ _ _ _ _
      ((trDat L κ τ hκ hτ).J f₁ (cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)))) = _
    rw [J_trD hκ hτ L, hJ p.1 (μsec p.2) hp (hsec.2 p.2 hζ).1, Formalism.MainNotions.FrameBoundFromBesselTorus.hsNormSq_smul]
  · intro γ hG
    refine ⟨ptTr κ τ hκ hτ γ, rfl, ?_, ?_⟩
    · rw [e1, e2, GPoint_ptTr]
    · rw [e1, e2, orbSq_trDat hκ hτ L f f₁ γ C fun g μR ν h1 h2 h3 h4 => hO γ g μR ν hG h1 h2 h3 h4]
      have hα := alphaPt_pos hκ hτ γ
      have hw := ptWeight_ptTr hk1 hκ hτ (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ
      have hcard := card_rootPat_le γ
      refine frames_ineqs (orbSq L f γ) (by positivity)
        (mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2)).le (inv_pos.mpr (by positivity))
        (ratio_le_frameFactor hκ hτ hCf hcard) (by rw [inv_inv]; exact ratio_inv_le_frameFactor hκ hτ hCf hcard) ?_
      have hP : 0 < κ ^ (2 * (rootPat γ).card) := pow_pos hκ _
      have hpw : ptWeight D.R.k D.R.rS (τ ^ 2 * Tz D.R.k D.R.rS L.z) (τ ^ 2 * Tz D.R.k D.R.rS L.z')
          (ptTr κ τ hκ hτ γ) = Wbig D.R.k D.R.rS κ τ * alphaPt κ τ γ ^ 2 *
            ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ / κ ^ (2 * (rootPat γ).card) := by
        rw [eq_div_iff hP.ne']; exact hw
      rw [hpw, wBig_eq_Wbig hk1, jacBig_eq, pow_add]
      field_simp

end Frames

end Formalism.MainNotions.OnePlaceExpansion
end
end

