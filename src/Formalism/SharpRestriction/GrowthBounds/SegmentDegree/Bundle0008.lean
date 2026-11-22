import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0001

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnConditionsOfNumericBounds
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateIndexInjective : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective (X.row j x) ∧ ∀ i, X.row j x i ∈ X.F.letters j ∧ Even (X.row j x i) ∧ X.row j x i < x

def EllDegreeLePowerBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j e, X.IsEll p K j e →
    X.dS K j e + X.dV K j e ≤ (r + K) * X.Ns * p ^ X.Rj p K j

def PowerExceedsMaxMultiplicity (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, X.mStar < p ^ X.Rj p K j

def ThresholdPowerLowerBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j b, X.Step2 p K j b → ∀ x ∈ X.toLate j,
      X.th p j x ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) * (X.thc p K j b x - (((r + K) * X.Ns : ℕ) : ℝ))

theorem mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    x ∈ X.toLate j ↔ x ∈ X.F.letters j ∧ ¬ X.F.IsW j x := by
  simp only [Dat.toLate, Finset.mem_filter]

section AG

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)
  [NeZero K] {R : Type} [Field R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (S : Set ℤ)

include hV

theorem vg_ellP : ((-(X.dS K j e : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.ellP K R j e) := by
  have h := vg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin r, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin r) R) ^ e (x, Fin.castAdd K c))
    (fun x => ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1))
    (fun x _ => vg_prod D hV S Finset.univ _ _ (fun c _ => vg_pow D hV S (vg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1)) =
      -(X.dS K j e : ℤ) := by
    unfold Dat.dS
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem lg_ellN : lam1S LZ S (X.ellN K R j e) ≤ (((X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  have h := lg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin K, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin K) R) ^ e (x, Fin.natAdd r c))
    (fun x => ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0))
    (fun x _ => lg_prod D hV S Finset.univ _ _ (fun c _ => lg_pow D hV S (lg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0)) =
      (X.dV K j e : ℤ) := by
    unfold Dat.dV
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem vg_DlSeg (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S) :
    (((X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.DlSeg p K R j) := by
  classical
  have h := vg_prod D hV (R := R) S (X.toLate j) (fun x' => X.detPl R j x' ^ X.sg p K j x')
    (fun x' => if x' = x then (X.sg p K j x : ℤ) else 0) (fun x' hx' => by
      by_cases hxx : x' = x
      · subst hxx
        rw [if_pos rfl]
        have h1 : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.detPl R j x') := by
          unfold Dat.detPl valS
          rw [sDegs_det LZ S _ (X.row j x') hinj (fun i => ⟨hS i, by simp [LZ, hev x' hx' i]⟩)]
          simp
        have := vg_pow D hV S h1 (X.sg p K j x')
        simpa using this
      · rw [if_neg hxx]
        have := vg_pow D hV S (vg_det D hV (R := R) S (X.row j x') (hev x' hx')) (X.sg p K j x')
        simpa [Dat.detPl] using this)
  rw [Finset.sum_ite_eq' (X.toLate j) x, if_pos hx] at h
  exact h

theorem vg_Aw (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S)
    (nu : Fin (segN X.F j + 1) → Fin r → ℤ) (I' : ℤ → Finset (Fin r)) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (segRen X.F j R r (Psi R nu I'))) :
    ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + -(X.dS K j e : ℤ) + (X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LZ S (X.Aw p K R j e nu I') := by
  unfold Dat.Aw
  exact vg_mul D hV S (vg_mul D hV S (vg_pow D hV S ha _) (vg_ellP D hV X K j e S))
    (vg_DlSeg D hV X p K j S hev x hx hinj hS)

theorem lg_Gw (ka : Fin (segN X.F j + 1) → Fin K → ℤ) (I'' : ℤ → Finset (Fin K)) (a : ℤ)
    (ha : lam1S LZ S (segRen X.F j R K (Psi R ka I'')) ≤ (a : WithBot ℤ)) :
    lam1S LZ S (X.Gw p K R j e ka I'') ≤ ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + (X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  unfold Dat.Gw
  exact lg_mul D hV S (lg_pow D hV S ha _) (lg_ellN D hV X K j e S)

end AG

theorem int_ineq (Q κ ν dS dV s mS kN : ℤ) (hQ : 0 ≤ Q) (h : κ + (kN + 1) ≤ ν) (hd : dS + dV ≤ kN * Q)
    (hm : mS < Q) : Q * κ + dV + (mS + s) ≤ Q * ν + -dS + s := by
  nlinarith [mul_le_mul_of_nonneg_left h hQ]

theorem geR_of_le {v : WithTop ℤ} {a : ℤ} {t : ℝ} (h : (a : WithTop ℤ) ≤ v) (ht : t ≤ (a : ℝ)) : geR v t := by
  unfold geR
  intro z hz
  rw [hz] at h
  have h' : a ≤ z := WithTop.coe_le_coe.mp h
  exact ht.trans (by exact_mod_cast h')

theorem column_conditions_of_numeric_bounds (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ)
    (hRow : LateIndexInjective) (hN0 : EllDegreeLePowerBound) (hN1 : PowerExceedsMaxMultiplicity C₀) (hN2 : ThresholdPowerLowerBound C₀) : ColumnConditionsWithMargin C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' ⊢
  have hF3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ),
      Formalism.MainNotions.CovariantDegrees.A3at (FF O) N n LL B th M := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  rw [← h1] at hI' hcond ⊢
  rw [← h2] at hI'' hcond ⊢
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (hF3 _ r _ b') P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (hF3 _ K _ b'') P2 I'' hI''
  obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi (FF O) P1.mu I') i
  obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi (FF O) P2.mu I'') i
  obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hM : X.Mw p K j e P2.mu (segE X.F j i) = ((p ^ X.Rj p K j : ℕ) : ℤ) *
      (if Even (segE X.F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) + (X.dV K j e : ℤ) :=
    (segE_strictMono X.F j).injective.extend_apply _ _ i
  have hrows := hRow p n' r K X hc.hX j
  have hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i) := fun x' hx' i => ((hrows x' hx').2 i).2.1
  have hinj := (hrows _ hxl).1
  have hlt : ∀ a, X.row j (segE X.F j i) a < segE X.F j i := fun a => ((hrows _ hxl).2 a).2.2
  have n0 := hN0 p n' r K X hc.hX j e hc.he
  have n1 := hN1 p n' r K X hc.hX hc.hLa hc.hk j
  have n2 := hN2 p n' r K X hc.hX hc.hLa hc.hk j b hc.h2 _ hxl
  have n0' : (X.dS K j e : ℤ) + (X.dV K j e : ℤ) ≤ (((r + K) * X.Ns : ℕ) : ℤ) * ((p ^ X.Rj p K j : ℕ) : ℤ) := by
    exact_mod_cast n0
  have n1' : (X.mStar : ℤ) < ((p ^ X.Rj p K j : ℕ) : ℤ) := by exact_mod_cast n1
  have hm0 : (X.m0 K : ℤ) = (((r + K) * X.Ns : ℕ) : ℤ) + 1 := by unfold Dat.m0; push_cast; ring
  have vlt := vg_Aw D hV X p K (R := FF O) j e {y | y < segE X.F j i} hev _ hxl hinj hlt P1.mu I'
    (P1.mu i.castSucc (lastIdx r)) (by rw [sA2]; exact (u1.2 i.castSucc).1)
  have vle := vg_Aw D hV X p K (R := FF O) j e {y | y ≤ segE X.F j i} hev _ hxl hinj (fun a => (hlt a).le) P1.mu I'
    (P1.mu i.succ (lastIdx r)) (by rw [sA1]; exact (u1.2 i.succ).1)
  refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
  · rw [hM, if_pos he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG3]; exact (u2.2 i.succ).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
    rw [hM, if_pos he]
    unfold Dat.mg
    have hce := (cE he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · rw [hM, if_neg he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG4]; exact (u2.2 i.castSucc).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
    rw [hM, if_neg he]
    unfold Dat.mg
    have hce := (cO he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · refine geR_of_le vlt ?_
    push_cast
    have hQ : (0 : ℝ) ≤ ((p : ℝ) ^ X.Rj p K j) := by positivity
    have n0r : (X.dS K j e : ℝ) + (X.dV K j e : ℝ) ≤ (((r : ℝ) + K) * X.Ns) * (p : ℝ) ^ X.Rj p K j := by
      exact_mod_cast n0
    have hdV : (0 : ℝ) ≤ (X.dV K j e : ℝ) := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ (X.sg p K j (segE X.F j i) : ℝ) := Nat.cast_nonneg _
    push_cast at n2
    have := mul_le_mul_of_nonneg_left cR hQ
    nlinarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamSatRestrict
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem lam_sat_restrict {O σ : Type} [CommRing O] [IsDomain O] (s : Set (σ →₀ ℕ)) (f : MvPolynomial σ O) (a : O)
    (ha : a ≠ 0) (h : a • f ∈ restrictSupport O s) : f ∈ restrictSupport O s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at h ⊢
  intro m hm
  apply h
  have hm' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hm)
  refine Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr ?_)
  rw [coeff_smul, smul_eq_mul]
  exact mul_ne_zero ha hm'

theorem lam_dvd_of_res {O σ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (P : MvPolynomial σ O) (h : MvPolynomial.map (IsLocalRing.residue O) P = 0) :
    ∃ z : MvPolynomial σ O, P = ϖ • z := by
  have hd : C ϖ ∣ P := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h1 : IsLocalRing.residue O (coeff m P) = 0 := by
      rw [← MvPolynomial.coeff_map, h, coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨z, hz⟩ := hd
  exact ⟨z, by rw [hz, smul_eq_C_mul]⟩

theorem restLamA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestLamA := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX j b hb
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hsatX := (h12 p O Sd n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hNK
    (fun _ => by positivity)).2.2.1
  have hsat : ∀ (f : SegRing O r K) (a : O), a ≠ 0 → a • f ∈ X.Mj p K O j b → f ∈ X.Mj p K O j b := by
    intro f a ha h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨⟨hsatX f a ha h1, lam_sat_restrict _ f a ha h2⟩, lam_sat_restrict _ f a ha h3⟩
  have hfin : Module.Finite O (X.Mj p K O j b) := restFin p n' r K X O j b hb
  have hfree : Module.Free O (X.Mj p K O j b) := Module.free_of_finite_type_torsion_free'
  let bs := Module.finBasis O (X.Mj p K O j b)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨fun i => (bs i : SegRing O r K), fun i => (bs i).2, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro cb hcb i
  choose c hc using fun i => IsLocalRing.residue_surjective (cb i)
  have h1 : MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • (bs i : SegRing O r K)) = 0 := by
    rw [sel_red_sum, ← hcb]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  obtain ⟨z, hz⟩ := lam_dvd_of_res hϖ _ h1
  have hzM : z ∈ X.Mj p K O j b := by
    refine hsat z ϖ hϖ.ne_zero ?_
    rw [← hz]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bs i).2
  have h2 : ∑ i, c i • bs i = ϖ • (⟨z, hzM⟩ : X.Mj p K O j b) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hz
  have h3 := congrArg (fun v => bs.repr v i) h2
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
  rw [← hc i, h3, map_mul]
  have : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  rw [this, zero_mul]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem sum_shift_le : ∀ (K : ℕ) [NeZero K] (f g : Fin K → ℤ), (∀ c, 0 ≤ g c) →
    (∀ (c : Fin K) (h : c.val + 1 < K), f ⟨c.val + 1, h⟩ ≤ g c) → ∑ c, f c ≤ f 0 + ∑ c, g c := by
  intro K
  cases K with
  | zero => intro h; exact absurd rfl (NeZero.ne (0 : ℕ))
  | succ K =>
    intro _ f g hg hfg
    rw [Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
    have h1 : ∑ c : Fin K, f c.succ ≤ ∑ c : Fin K, g c.castSucc :=
      Finset.sum_le_sum fun c _ => hfg c.castSucc (by simp)
    have h2 := hg (Fin.last K)
    linarith

theorem int_pos_neg (x : ℤ) : x = max x 0 - max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

variable {N r K : ℕ}

theorem posS_split (la : Fin (r + K) → ℤ) :
    posS la = ∑ c : Fin r, max (la (Fin.castAdd K c)) 0 + ∑ c : Fin K, max (la (Fin.natAdd r c)) 0 := by
  unfold posS; rw [Fin.sum_univ_add]

theorem negS_split (la : Fin (r + K) → ℤ) :
    negS la = ∑ c : Fin r, max (-la (Fin.castAdd K c)) 0 + ∑ c : Fin K, max (-la (Fin.natAdd r c)) 0 := by
  unfold negS; rw [Fin.sum_univ_add]

theorem dplus_le_geom {LL : Letters (Fin N)} {B : Fin N → ℕ} {n0 p : ℕ} (hp : 13 ≤ p)
    (H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)) :
    ∀ (m : ℕ) (l : Fin N), LL.vec l = true → m ≤ l.val → l.val < n0 →
      (dplus LL B m : ℝ) ≤ 10 / (p : ℝ) ^ 2 * (B l : ℝ) := by
  have hp' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  intro m
  induction m with
  | zero =>
    intro l _ _ _
    have : dplus LL B 0 = 0 := by unfold dplus; simp
    rw [this]; push_cast; positivity
  | succ m ih =>
    intro l hl hml hln
    have hmN : m < N := by have := l.2; omega
    have hd : dplus LL B (m + 1) = dplus LL B m + if LL.vec ⟨m, hmN⟩ = true then B ⟨m, hmN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B m hmN
    rw [hd]
    by_cases hv : LL.vec ⟨m, hmN⟩ = true
    · rw [if_pos hv]
      have h1 := ih ⟨m, hmN⟩ hv le_rfl (by simp only; omega)
      have h2 := H2 ⟨m, hmN⟩ l (by rw [Fin.lt_def]; simp only; omega) hln (by rw [hv, hl])
      push_cast
      have hB : (0 : ℝ) ≤ (B ⟨m, hmN⟩ : ℝ) := Nat.cast_nonneg _
      have h3 : (B ⟨m, hmN⟩ : ℝ) ≤ 5 / (p : ℝ) ^ 2 * (B l : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : (p : ℝ) ^ 2 / 5 * (B ⟨m, hmN⟩ : ℝ) = (B ⟨m, hmN⟩ : ℝ) * (p : ℝ) ^ 2 / 5 := by ring
        rw [this, div_le_iff₀ (by norm_num)] at h2
        linarith
      have h4 : 10 / (p : ℝ) ^ 2 ≤ 10 / 169 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
      have h5 : 10 / (p : ℝ) ^ 2 * (B ⟨m, hmN⟩ : ℝ) ≤ 10 / 169 * (B ⟨m, hmN⟩ : ℝ) :=
        mul_le_mul_of_nonneg_right h4 hB
      have h6 : 10 / (p : ℝ) ^ 2 * (B l : ℝ) = 2 * (5 / (p : ℝ) ^ 2 * (B l : ℝ)) := by ring
      rw [h6]
      linarith
    · rw [if_neg hv]
      simpa using ih l hl (by omega) hln

theorem oldest_lt_n0 {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}
    (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) : (od i).val < n0 := by
  by_contra hcon
  have h1 := H.od_card i hi
  have h2 : (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card ≤
      (Finset.Ico (od i) i).card := by
    refine Finset.card_le_card ?_
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact Finset.mem_Ico.mpr ⟨hl.1, hl.2.1⟩
  rw [Fin.card_Ico] at h2
  have := i.2
  have := H.hN
  omega

theorem vcount_od {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}
    (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) :
    vcount LL ((od i).val + 1) i.val + 1 = r := by
  classical
  have h1 := H.od_card i hi
  have h2 : (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true) =
      insert (od i) (Finset.univ.filter fun l : Fin N => (od i).val + 1 ≤ l.val ∧ l.val < i.val ∧ LL.vec l = true) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hl : l = od i
      · exact Or.inl hl
      · refine Or.inr ⟨?_, h2, h3⟩
        have : (od i).val ≠ l.val := fun h => hl (Fin.ext h.symm)
        have h1' : (od i).val ≤ l.val := h1
        omega
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨le_rfl, H.od_lt i hi, H.od_vec i hi⟩
      · exact ⟨by rw [Fin.le_def]; omega, h2, h3⟩
  rw [h2, Finset.card_insert_of_notMem (by simp)] at h1
  exact h1

theorem nu_last_le [NeZero r] {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ}
    {a La : ℝ} {p : ℕ} (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (i : Fin N) (hi : r ≤ i.val) :
    ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) ≤ 2 * (B (od i) : ℝ) := by
  have hr := H.r1
  have hod := oldest_lt_n0 H i hi
  have hvc := vcount_od H i hi
  have hlt : (od i).val < i.val := H.od_lt i hi
  have h1 := row_back P ((od i).val + 1) i.val (by omega) (by have := i.2; omega) ⟨0, by omega⟩
    (Fin.castAdd K (lastIdx r)) (by simp [lastIdx]; omega)
  have h2 := mu_le_dplus P ((od i).val + 1) (by have := i.2; omega) ⟨0, by omega⟩
  have h3 : dplus LL dd ((od i).val + 1) = dplus LL B ((od i).val + 1) := by
    unfold dplus
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < (od i).val + 1 ∧ LL.vec l = true
    · rw [if_pos hl, if_pos hl, hdd l (by omega)]
    · rw [if_neg hl, if_neg hl]
  have h4 : dplus LL B ((od i).val + 1) = dplus LL B (od i).val + B (od i) := by
    have := dsum_succ (fun l => LL.vec l = true) B (od i).val (od i).2
    rw [if_pos (H.od_vec i hi)] at this
    exact this
  have h5 := dplus_le_geom H.p13 H.H2 (od i).val (od i) (H.od_vec i hi) le_rfl hod
  have hp' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast H.p13
  have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have h6 : 10 / (p : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hB : (0 : ℝ) ≤ (B (od i) : ℝ) := Nat.cast_nonneg _
  have h7 : (plPart P.mu i.castSucc (lastIdx r) : ℤ) ≤ (dplus LL dd ((od i).val + 1) : ℤ) := le_trans h1 h2
  have h8 : ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) ≤ ((dplus LL dd ((od i).val + 1) : ℕ) : ℝ) := by
    exact_mod_cast h7
  rw [h3, h4] at h8
  push_cast at h8
  have h9 : 10 / (p : ℝ) ^ 2 * (B (od i) : ℝ) ≤ 1 * (B (od i) : ℝ) := mul_le_mul_of_nonneg_right h6 hB
  linarith

theorem typical_path_orders_small : TypicalPathOrdersSmall := by
  intro N n0 r K _ _ LL B od bb a La p H μ hμ hTyp i hi
  obtain ⟨dd, hP⟩ := hμ
  obtain ⟨P, rfl⟩ := hP.path
  have hr := H.r1
  have hK := H.N_add_r_le_K
  have F1 : ∀ (s : Fin (N + 1)) (m : Fin (r + K)), m.val ≤ r → 0 ≤ P.mu s m := by
    intro s m hm
    exact mu_nonneg P s.val s.2 m (by have := s.2; omega)
  obtain ⟨hT1, hT2, hT3⟩ := hTyp i
  refine ⟨hT3 hi, ?_, ?_⟩
  · intro hv
    have hstep := step_vec P i hv
    have hX := hT2 hv hi

    have hneg : ∀ s : Fin (N + 1), negS (P.mu s) = ∑ c : Fin K, max (-tanPart P.mu s c) 0 := by
      intro s
      rw [negS_split]
      have : ∑ c : Fin r, max (-P.mu s (Fin.castAdd K c)) 0 = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        have := F1 s (Fin.castAdd K c) (by simp)
        exact max_eq_right (by linarith)
      rw [this, zero_add]; rfl
    have hshift : ∑ c : Fin K, max (tanPart P.mu i.succ c) 0 ≤
        max (tanPart P.mu i.succ 0) 0 + ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0 := by
      refine sum_shift_le K (fun c => max (tanPart P.mu i.succ c) 0) (fun c => max (tanPart P.mu i.castSucc c) 0)
        (fun c => le_max_right _ _) ?_
      intro c h
      refine max_le_max ?_ le_rfl
      have := hstep.2.1 (Fin.natAdd r c) (by simp; omega)
      exact this
    have hfirst : tanPart P.mu i.succ 0 ≤ plPart P.mu i.castSucc (lastIdx r) := by
      have := hstep.2.1 (Fin.castAdd K (lastIdx r)) (by simp [lastIdx]; omega)
      have he : (⟨(Fin.castAdd K (lastIdx r)).val + 1, by simp [lastIdx]; omega⟩ : Fin (r + K)) =
          Fin.natAdd r (0 : Fin K) := by
        apply Fin.ext; simp [lastIdx]; omega
      rw [he] at this
      exact this
    have hnn : 0 ≤ plPart P.mu i.castSucc (lastIdx r) := F1 _ _ (by simp [lastIdx])
    have hsum : ∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) =
        (∑ c : Fin K, max (tanPart P.mu i.succ c) 0 - ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0) +
        (negS (P.mu i.castSucc) - negS (P.mu i.succ)) := by
      rw [hneg, hneg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := int_pos_neg (tanPart P.mu i.succ c)
      have h2 := int_pos_neg (tanPart P.mu i.castSucc c)
      linarith
    have hle : ∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) ≤
        plPart P.mu i.castSucc (lastIdx r) + (negS (P.mu i.castSucc) - negS (P.mu i.succ)) := by
      rw [hsum]
      have : max (tanPart P.mu i.succ 0) 0 ≤ plPart P.mu i.castSucc (lastIdx r) := max_le hfirst hnn
      linarith
    have hle' : ((∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) : ℤ) : ℝ) ≤
        ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) + ((negS (P.mu i.castSucc) - negS (P.mu i.succ) : ℤ) : ℝ) := by
      exact_mod_cast hle
    have hnu := nu_last_le H P hP.degs i hi
    linarith
  · intro hv
    have hstep := step_cov P i hv
    have hX := hT1 hv
    have hpos : ∀ s : Fin (N + 1), posS (P.mu s) = ∑ c : Fin r, plPart P.mu s c +
        ∑ c : Fin K, max (tanPart P.mu s c) 0 := by
      intro s
      rw [posS_split]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      exact max_eq_left (F1 s (Fin.castAdd K c) (by simp))
    have hmono : ∑ c : Fin K, max (tanPart P.mu i.succ c) 0 ≤ ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0 :=
      Finset.sum_le_sum fun c _ => max_le_max (hstep.1 (Fin.natAdd r c)) le_rfl
    have hle : ∑ c, (plPart P.mu i.castSucc c - plPart P.mu i.succ c) ≤
        posS (P.mu i.castSucc) - posS (P.mu i.succ) := by
      rw [hpos, hpos, Finset.sum_sub_distrib]
      linarith
    have hle' : ((∑ c, (plPart P.mu i.castSucc c - plPart P.mu i.succ c) : ℤ) : ℝ) ≤
        ((posS (P.mu i.castSucc) - posS (P.mu i.succ) : ℤ) : ℝ) := by exact_mod_cast hle
    linarith

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

