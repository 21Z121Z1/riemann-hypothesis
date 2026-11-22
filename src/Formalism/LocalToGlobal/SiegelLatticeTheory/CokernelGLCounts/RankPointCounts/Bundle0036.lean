import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0034
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadMAddCorner
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

section LeadLemmas

variable {K K' : Type*} [CommRing K] [CommRing K']

theorem det_map' {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

theorem leadM_top {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : leadM A (r + 1) = A.det := by
  unfold leadM; rw [dif_pos le_rfl]; rfl

theorem leadM_map {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (A.map f) l = f (leadM A l) := by
  unfold leadM
  split_ifs with hl
  · rw [RingHom.map_det]; rfl
  · simp

theorem leadM_smul {m : ℕ} (c : K) (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (c • A) l = c ^ l * leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [show (c • A).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • A.submatrix (Fin.castLE hl) (Fin.castLE hl)
      from rfl, Matrix.det_smul, Fintype.card_fin]
  · simp

theorem leadM_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) K) (l : ℕ) : leadM A.transpose l = leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [← Matrix.det_transpose]; rfl
  · rfl

theorem castLE_ne_last {r : ℕ} (a : Fin r) : Fin.castLE (Nat.le_succ r) a ≠ Fin.last r := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.isLt
  simp at h1
  omega

theorem leadM_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    leadM (A + c • Ecorner r) r = leadM A r := by
  unfold leadM
  rw [dif_pos (Nat.le_succ r), dif_pos (Nat.le_succ r)]
  congr 1
  ext a b
  simp [Ecorner, castLE_ne_last a]

theorem det_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + c • Ecorner r).det = A.det + c * leadM A r := by
  have hE : A + c • Ecorner r =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ecorner]
      · simp [Ecorner, hb]
    · simp [Ecorner, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r)) := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
    rfl
  rw [hs, leadM, dif_pos (Nat.le_succ r)]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

end LeadLemmas

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem leadZZ_model (M : Loc.Model F E) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (leadM Zh r = 0 ↔ leadM (Loc.HermSp.ZZplusOf M Zh T T') r = 0) ∧
    (IsUnit (leadM Zh r) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf M Zh T T') r)) ∧
    (leadM Zh r = 0 → IsUnit (leadM Zh (r + 1)) → IsUnit (Loc.HermSp.ZZplusOf M Zh T T').det) := by
  rcases hs : M.split with _ | g
  · have e : Loc.HermSp.ZZplusOf M Zh T T' = Zh := by unfold Loc.HermSp.ZZplusOf; rw [hs]
    rw [e, ← leadM_top]
    exact ⟨Iff.rfl, Iff.rfl, fun _ h => h⟩
  · set q : F := (g.q : F) with hq
    have hq0 : q ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    let π₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
    let π₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
    have hzero : ∀ x : E, x = 0 ↔ π₁ x = 0 ∧ π₂ x = 0 := by
      intro x
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, h2⟩
        have : g.e x = 0 := Prod.ext h1 h2
        exact (map_eq_zero_iff g.e g.e.injective).1 this
    have hunit : ∀ x : E, IsUnit x ↔ π₁ x ≠ 0 ∧ π₂ x ≠ 0 := by
      intro x
      rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
      rfl
    have e1 : (Loc.HermSp.ZZplusOf M Zh T T').map π₁ = q⁻¹ • Zh.map π₁ + (T / q) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have e2 : (Loc.HermSp.ZZplusOf M Zh T T').map π₂ = (-q⁻¹) • (Zh.map π₂).transpose + (-(T' / q)) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have l1 : π₁ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = q⁻¹ ^ r * π₁ (leadM Zh r) := by
      rw [← leadM_map, e1, leadM_add_corner, leadM_smul, leadM_map]
    have l2 : π₂ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = (-q⁻¹) ^ r * π₂ (leadM Zh r) := by
      rw [← leadM_map, e2, leadM_add_corner, leadM_smul, leadM_transpose, leadM_map]
    have hq1 : q⁻¹ ^ r ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
    have hq2 : (-q⁻¹) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))
    refine ⟨?_, ?_, ?_⟩
    · rw [hzero, hzero (leadM _ r), l1, l2, mul_eq_zero, mul_eq_zero]
      simp [hq0]
    · rw [hunit, hunit (leadM _ r), l1, l2]
      simp [hq0]
    · intro h0 hu
      rw [leadM_top] at hu
      rw [hunit] at hu ⊢
      have z := (hzero _).1 h0
      rw [← det_map', ← det_map', e1, e2, det_add_corner, det_add_corner, leadM_smul, leadM_smul,
        leadM_transpose, leadM_map, leadM_map, z.1, z.2, Matrix.det_smul, Matrix.det_smul,
        Matrix.det_transpose, det_map', det_map']
      simp only [mul_zero, add_zero, Fintype.card_fin]
      exact ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hu.1,
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))) hu.2⟩

end Model

theorem leadZZ_holds {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : LeadZZ Zd :=
  fun p Zh T T' => leadZZ_model (Zd.M p) Zh T T'

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocRealAtOrd
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def LocRealAt (p : PlF D) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)), IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w O →
    ∃ (Lp Up : MatP D p) (c : 𝓞 D.host.F), c ≠ 0 ∧ IsLo Lp ∧ IsUp Up ∧
      ∀ L U : PairVal.MatR D, IsLo L → IsUp U →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (L a b) - Lp a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (U a b) - Up a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        tupZ M δ u u' (L * ptMat w * U * Sg D.host.E D.R.rS) p = O

variable {M δ}

theorem locRealAt_ord (hA : ∀ p, Agree δ M p) (p : PlF D) (hM : (M p).split = none) : LocRealAt M δ u u' p :=
  fun w O hO => locReal_ord hA u u' w p hM O hO

theorem adj_mem {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} {l : Matrix (Fin n) (Fin n) R}
    (hl : ∀ a b, l a b ∈ S) (a b : Fin n) : l.adjugate a b ∈ S := by
  let lR : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, hl a b⟩
  have h1 : lR.map S.subtype = l := by ext a b; rfl
  have h2 := congrFun (congrFun (RingHom.map_adjugate S.subtype lR) a) b
  rw [← h1, show lR.map S.subtype = S.subtype.mapMatrix lR from rfl, ← h2]
  exact (lR.adjugate a b).2

theorem congr_dvd {p : PlF D} {y : (D.s.atP p).Ep} {c c' r : 𝓞 D.host.F} (hc : c = c' * r)
    (h : ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) :
    ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c')) * o := by
  obtain ⟨o, ho, rfl⟩ := h
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F r)) * o,
    Subring.mul_mem _ (alg_mem_O (fun q => D.s.atP q) p (iotaF_int_mem (fun q => D.s.atP q) p r)) ho, ?_⟩
  rw [hc, map_mul, map_mul, map_mul, mul_assoc]

theorem exist_of (hA : ∀ p, Agree δ M p) (hTy : ∀ p, (M p).split ≠ none → LocRealAt M δ u u' p) :
    Exist M δ u u' := by
  intro w' _ x hx
  have hLR : ∀ p, LocRealAt M δ u u' p := fun p => by
    by_cases h : (M p).split = none
    · exact locRealAt_ord u u' hA p h
    · exact hTy p h
  have hloc := fun p => hLR p w' (x.1 p) (hx p)
  choose Lp Up cp hcp0 hLp hUp hreal using hloc
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  have hBad := Filter.eventually_cofinite.1 hgood
  set S : Finset (PlF D) := x.2.toFinset ∪ hBad.toFinset with hS
  set c : 𝓞 D.host.F := ∏ p ∈ S, cp p with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hcp0 p
  obtain ⟨L, hL1, hL0, hLS, hLO⟩ := approx_lo (fun q => D.s.atP q) S c hc0 (fun p => Lp p)
    (fun p _ a => (hLp p).1 a) (fun p _ a b hab => (hLp p).2 a b hab)
  obtain ⟨U, hU1, hU0, hUS, hUO⟩ := approx_up (fun q => D.s.atP q) S c hc0 (fun p => Up p)
    (fun p _ a => (hUp p).1 a) (fun p _ a b hab => (hUp p).2 b a hab)
  have hLlo : IsLo L := ⟨hL1, hL0⟩
  have hUup : IsUp U := ⟨hU1, fun a b hab => hU0 b a hab⟩
  have hZ : (L * ptMat w' * U * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w' * U := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  refine ⟨L * ptMat w' * U * Sg D.host.E D.R.rS, ⟨L, U, fun i j => ⟨hL0 i j, fun h => h ▸ hL1 i⟩,
    fun i j => ⟨hU0 i j, fun h => h ▸ hU1 i⟩, by rw [zhatOM_eq]; exact hZ⟩, ?_⟩
  funext p
  by_cases hp : p ∈ S
  · have hsplit : c = cp p * ∏ q ∈ S.erase p, cp q := (Finset.mul_prod_erase S cp hp).symm
    exact hreal p L U hLlo hUup (fun a b => congr_dvd hsplit (hLS p hp a b))
      (fun a b => congr_dvd hsplit (hUS p hp a b))
  · have hpx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_left _ (x.2.mem_toFinset.2 h))
    have hpg : (M p).split = none ∧ (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
        ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
          (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
        ∀ t ∈ (∅ : Finset D.host.E), ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
          (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
            (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O := by
      by_contra h
      exact hp (Finset.mem_union_right _ (hBad.mem_toFinset.2 h))
    have hentL : ∀ a b, (D.s.atP p).ιE (L a b) ∈ (D.s.atP p).O := hLO p hp
    have hentU : ∀ a b, (D.s.atP p).ιE (U a b) ∈ (D.s.atP p).O := hUO p hp
    have hLd : L.det = 1 := det_lo' hLlo
    have hUd : U.det = 1 := det_up' hUup
    have hinv : ∀ (X : PairVal.MatR D), X.det = 1 → (∀ a b, (D.s.atP p).ιE (X a b) ∈ (D.s.atP p).O) →
        ∀ a b, (D.s.atP p).ιE (X⁻¹ a b) ∈ (D.s.atP p).O := by
      intro X hX hXe a b
      rw [Matrix.inv_def, hX, Ring.inverse_one, one_smul]
      have h2 := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE X) a) b
      rw [show ((D.s.atP p).ιE.mapMatrix X.adjugate) a b = (D.s.atP p).ιE (X.adjugate a b) from rfl] at h2
      rw [h2]
      exact adj_mem (D.s.atP p).O (fun a b => hXe a b) a b
    rw [hpx]
    exact tupZ_eq_x0L_at hA u u' hLlo hUup hZ p hpg.1 hpg.2.1.1 hpg.2.1.2 hpg.2.2.1.1 hpg.2.2.1.2
      (fun a b => ⟨hentL a b, hentU a b, hinv L hLd hentL a b, hinv U hUd hentU a b⟩)

end Assembly

end Formalism.L2.SG.Pf.PCountEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapInvMul
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Comp

variable {E : Type*} [Field E] {K : Type*} [CommRing K] (ψ : E →+* K) {r : ℕ}

def cP (cv : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv * L₁.map ψ

def cP' (cv' : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  L₁⁻¹.map ψ * Matrix.diagonal cv'

def cQ (cv : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  U₁.map ψ * Matrix.diagonal cv

def cQ' (cv' : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv' * U₁⁻¹.map ψ

theorem diag_one {cv cv' : Fin (r + 1) → K} (h : ∀ a, cv a * cv' a = 1) :
    Matrix.diagonal cv * Matrix.diagonal cv' = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext h)

theorem map_one' : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).map ψ = 1 := Matrix.map_one _ ψ.map_zero ψ.map_one

theorem map_inv_mul {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L⁻¹.map ψ * L.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (by rw [h]; exact isUnit_one), map_one']

theorem map_mul_inv {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L.map ψ * L⁻¹.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (by rw [h]; exact isUnit_one), map_one']

theorem mono_map (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    (mono σ ν).map ψ = mono σ (fun a => ψ (ν a)) := by
  ext a b
  simp only [Matrix.map_apply, mono, Matrix.of_apply]
  split_ifs <;> simp

theorem inv_eq_map {x : E} (hx : x ≠ 0) : Ring.inverse (ψ x) = ψ x⁻¹ := by
  have h1 : ψ x * ψ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  calc Ring.inverse (ψ x) = Ring.inverse (ψ x) * (ψ x * ψ x⁻¹) := by rw [h1, mul_one]
    _ = ψ x⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ ⟨⟨ψ x, ψ x⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩, one_mul]

theorem hcv'_of {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) : ∀ a, cv' a * cv a = 1 :=
  fun a => by rw [mul_comm]; exact hcv a

variable {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) {L₁ U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
include hcv hL₁ hU₁

theorem conjPrime_conjPrime₂ : cP ψ cv L₁ * cP' ψ cv' L₁ = 1 := by
  unfold cP cP'
  rw [show Matrix.diagonal cv * L₁.map ψ * (L₁⁻¹.map ψ * Matrix.diagonal cv') =
      Matrix.diagonal cv * (L₁.map ψ * L₁⁻¹.map ψ) * Matrix.diagonal cv' by simp only [Matrix.mul_assoc],
    map_mul_inv ψ (det_lo hL₁), Matrix.mul_one, diag_one hcv]

theorem cP'_cP : cP' ψ cv' L₁ * cP ψ cv L₁ = 1 := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc],
    diag_one (hcv'_of hcv), Matrix.mul_one, map_inv_mul ψ (det_lo hL₁)]

theorem cQ_cQ' : cQ ψ cv U₁ * cQ' ψ cv' U₁ = 1 := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc],
    diag_one hcv, Matrix.mul_one, map_mul_inv ψ (det_up hU₁)]

theorem cQ'_cQ : cQ' ψ cv' U₁ * cQ ψ cv U₁ = 1 := by
  unfold cQ cQ'
  rw [show Matrix.diagonal cv' * U₁⁻¹.map ψ * (U₁.map ψ * Matrix.diagonal cv) =
      Matrix.diagonal cv' * (U₁⁻¹.map ψ * U₁.map ψ) * Matrix.diagonal cv by simp only [Matrix.mul_assoc],
    map_inv_mul ψ (det_up hU₁), Matrix.mul_one, diag_one (hcv'_of hcv)]

theorem cP_lo {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsLo k) : IsLo (cP' ψ cv' L₁ * k * cP ψ cv L₁) := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * k * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * k * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc]]
  exact isLo_mul (isLo_mul (isLo_map ψ (isLo_inv hL₁)) (isLo_conj hk cv' cv (hcv'_of hcv))) (isLo_map ψ hL₁)

theorem cQ_up {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsUp k) : IsUp (cQ ψ cv U₁ * k * cQ' ψ cv' U₁) := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * k * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * k * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc]]
  exact isUp_mul (isUp_mul (isUp_map ψ hU₁) (isUp_conj hk cv cv' hcv)) (isUp_map ψ (isUp_inv hU₁))

theorem cW_eq (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) (s e : K) :
    s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r =
      s • (cP ψ cv L₁ * mono σ (fun a => ψ (ν a)) * cQ ψ cv U₁) - e • Ecorner r := by
  unfold cP cQ
  rw [Matrix.map_mul, Matrix.map_mul, mono_map]
  simp only [Matrix.mul_assoc]

theorem cG_eq (X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cP' ψ cv' L₁ * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv') * cP ψ cv L₁ = X'.map ψ := by
  have e : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Matrix.diagonal cv' * (Matrix.diagonal cv * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, diag_one (hcv'_of hcv), Matrix.one_mul]
  have f : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, L₁⁻¹.map ψ * (L₁.map ψ * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, map_inv_mul ψ (det_lo hL₁), Matrix.one_mul]
  unfold cP cP'
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc, e, f, map_inv_mul ψ (det_lo hL₁), Matrix.mul_one]

theorem conj_mul {P P' A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hPP : P * P' = 1) :
    P' * (A * B) * P = (P' * A * P) * (P' * B * P) := by
  rw [show P' * A * P * (P' * B * P) = P' * A * (P * P') * B * P by simp only [Matrix.mul_assoc], hPP,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem comp_target {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hkL : IsLo kL)
    (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) :
    IsLo (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ ∧ (∀ i j, σ j < σ i → (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ i j = 0) ∧
      (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ = 1 := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  rw [cW_eq ψ hcv hL₁ hU₁] at hk
  have hfix := stab_core hs (cP'_cP ψ hcv hL₁ hU₁) (cQ_cQ' ψ hcv hL₁ hU₁) hkL hkR hk
  exact fix_inv hσ hν' (cP_lo ψ hcv hL₁ hU₁ hkL) (cQ_up ψ hcv hL₁ hU₁ hkR) hfix

theorem comp_main {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {I : Subring K} {kL kR a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * b =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    {X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (haX : a = kL * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv'))
    {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ψ (ν a) ∈ I) (hbν' : ∀ a, t * ψ (ν a)⁻¹ ∈ I)
    (bP : ∀ i j, t * cP ψ cv L₁ i j ∈ I) (bP' : ∀ i j, t * cP' ψ cv' L₁ i j ∈ I)
    (bQ : ∀ i j, t * cQ ψ cv U₁ i j ∈ I) (bQ' : ∀ i j, t * cQ' ψ cv' U₁ i j ∈ I)
    (bx : ∀ i j, t * (cP' ψ cv' L₁ * kL * cP ψ cv L₁) i j ∈ I)
    (hG : EntIn (lat I (t * (t * (t * (t * (t * c)))))) (X'.map ψ - (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  have hinv : ∀ x, t * Ring.inverse (ψ (ν x)) ∈ I := fun x => by
    rw [inv_eq_map ψ (hν x)]
    exact hbν' x
  have hT := (comp_target ψ hcv hL₁ hU₁ hσ hν hs hkL hkR hk).2.2
  have hA : cP' ψ cv' L₁ * a * cP ψ cv L₁ = (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * X'.map ψ := by
    rw [haX, conj_mul hcv hL₁ hU₁ (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁), cG_eq ψ hcv hL₁ hU₁]
  have hE := close_of_target hT bx hG
  rw [← hA] at hE
  rw [cW_eq ψ hcv hL₁ hU₁] at hab
  exact close_pair hσ hν' ht hc hbν hinv (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁) (cP'_cP ψ hcv hL₁ hU₁)
    (cQ_cQ' ψ hcv hL₁ hU₁) (cQ'_cQ ψ hcv hL₁ hU₁) bP bP' bQ bQ' hs ha hb hab (cP_lo ψ hcv hL₁ hU₁ ha)
    (cQ_up ψ hcv hL₁ hU₁ hb) hE

end Comp

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

