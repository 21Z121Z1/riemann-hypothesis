import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.LocalToGlobal.Columns.Bundle0035
import Formalism.LocalToGlobal.Columns.Bundle0027
import Formalism.LocalToGlobal.Columns.Bundle0026

-- bundled from Formalism.LocalToGlobal.Columns.ChainInstS
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

theorem LocE.symmetric_level_bound_le (k₀ rS s : ℕ) : LocE.bd5 k₀ rS s ≤ s := by
  unfold LocE.bd5
  split_ifs <;> omega

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def symPhiCond (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (k₀ rS r t j c n : ℕ) (M : ℕ → ℕ → E) : Prop :=
  (∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (M p p')) ∧
    (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (M p p' / (q : E))) ∧
    (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
      (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
    (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)

open Classical in
theorem phiGS_eq (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x =
      if symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) then
        LocE.lamGvS ψ₀ χ k₀ r t (j - 1) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) *
          (LocE.unitV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
            LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)))⁻¹
      else 0 := rfl

theorem symFPos_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fPos k₀ c n (LocE.fIdx k₀ c n p) = p := by
  unfold LocE.fPos LocE.fIdx
  split_ifs <;> omega

theorem symFIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem JGsym_entry (hq0 : (q : E) ≠ 0) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS ≤ r)
    {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n c) {p p' : ℕ} (hp : p < n + c) (hp' : p' < r) (hpn : p' < n + c)
    (hb : symIdx k₀ rS p' ≤ symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) :
    IntAt P ((LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p' - if p = p' then 1 else 0) / (q : E)) := by
  have hm := (hκ.2.2 (symIdx k₀ rS p') (symIdx_lt hr hp')).2
  unfold LocE.bvecS LocE.flagS at hm
  rw [symIdxInv_symIdx, ciMem_sclLat] at hm
  have h3 := hm ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩
  have hbd : LocE.bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS p := by
    rcases hb with hb | ⟨h1, h2⟩
    · exact le_trans (LocE.symmetric_level_bound_le _ _ _) hb
    · subst h1
      unfold LocE.bd5 symIdx
      split_ifs <;> omega
  simp only [symFPos_fIdx hk hp, if_pos hbd] at h3
  unfold LocE.bvecG at h3
  rw [map_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at h3
  have hat : Loc.atN (κ.toLinearMap (Loc.eN E (n + c) (LocE.fIdx k₀ c n p'))) (LocE.fIdx k₀ c n p) =
      κ (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ := by
    unfold Loc.atN
    rw [dif_pos (symFIdx_lt hk hp)]
    rfl
  unfold LocE.entB
  rw [hat]
  generalize κ (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ = Xv at h3 ⊢
  have he : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ = if p = p' then 1 else 0 := by
    unfold Loc.eN
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpp, if_neg]
      intro h
      apply hpp
      have h' : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' := h
      have h1 := symFPos_fIdx (c := c) hk hp
      have h2 := symFPos_fIdx (c := c) hk hpn
      rw [h'] at h1
      omega
  rw [he] at h3
  have e : ((q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p) + 1))⁻¹ *
      ((q : E) ^ LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') * Xv -
        (q : E) ^ LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') * (if p = p' then 1 else 0)) =
      (Xv * (q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') - LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) -
        if p = p' then 1 else 0) / (q : E) := by
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, sub_self, zpow_zero, zpow_add₀ hq0, zpow_one]
      have hA := zpow_ne_zero (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) hq0
      field_simp
    · rw [if_neg hpp, zpow_sub₀ hq0, zpow_add₀ hq0, zpow_one]
      have hA := zpow_ne_zero (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) hq0
      field_simp
      ring
  rw [← e]
  exact h3

theorem JGsym_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS ≤ r)
    {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n c) {p p' : ℕ} (hp : p < n + c) (hp' : p' < r) (hpn : p' < n + c)
    (hne : p ≠ p') (hb : symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) :
    redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') = 0 := by
  have h := JGsym_entry hq0 hk hr hκ hp hp' hpn (hb.imp le_of_lt id)
  rw [if_neg hne, sub_zero] at h
  exact (ciRed_of_div hq hq0 h).2

theorem phiGS_col (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ rS r t j c' n' c n : ℕ} (hkr : k₀ < r) (x : HomE E (n' + c') (n + c)) (h : LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x ≠ 0)
    {p : ℕ} (hp : p < n + c) :
    IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p k₀) ∧
      redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p k₀) = if p = k₀ then 1 else 0 := by
  classical
  rw [phiGS_eq] at h
  have hC := (ite_ne_right_iff.1 h).1
  have hka : k₀ < r + (j - 1) * t := Nat.lt_of_lt_of_le hkr (Nat.le_add_right _ _)
  refine ⟨hC.1 p k₀ hp hka, ?_⟩
  by_cases hpk : p = k₀
  · rw [if_pos hpk, hpk]
    exact (hC.2.2.1 k₀ hkr).1
  · rw [if_neg hpk]
    by_cases hpa : p < r + (j - 1) * t
    · refine (hC.2.2.1 k₀ hkr).2 p hpa hpk (Or.inr ?_)
      unfold symIdx
      by_cases h0 : rS = 0
      · subst h0
        by_cases hlt : p < k₀
        · exact Or.inr ⟨rfl, hlt⟩
        · left
          split_ifs <;> omega
      · left
        split_ifs <;> omega
    · exact (ciRed_of_div hq hq0 (hC.2.1 p k₀ (Nat.le_of_not_lt hpa) hp hka)).2

theorem symEntB_join_col (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) {p : ℕ} (hp : p < n) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p k₀ = (q : E) * y' ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' k₀ = n' := by
    unfold LocE.fIdx
    rw [if_neg (lt_irrefl _), if_pos (by omega)]
    omega
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, dif_pos (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) n') = (0 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) n' (Fin.castAdd 1 i) = 0
    unfold Loc.eN
    simp only [Fin.val_castAdd]
    rw [if_neg (by have := i.2; omega)]
  have e2 : Loc.eN E (n' + 1) n' ⟨n', by omega⟩ = 1 := by
    unfold Loc.eN
    rw [if_pos rfl]
  have e3 : LocE.scE n' (fun i => i + 1) n' = 1 := by simp [LocE.scE]
  rw [e1, e2, e3, map_zero, Pi.zero_apply, zero_add, one_mul, sub_zero, zpow_one, mul_comm]

def LamGBSChar (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j n c : ℕ) : Prop :=
  ∀ κ ∈ LocE.JGsym P q k₀ rS r t n c, ∀ κ' ∈ LocE.JGsym P q k₀ rS r t n c,
    LocE.lamGBS q ψ₀ χ k₀ r t j n c ((κ * κ' : Sp E (n + c) ≃ₗ[E] Sp E (n + c))).toLinearMap =
      LocE.lamGBS q ψ₀ χ k₀ r t j n c κ.toLinearMap * LocE.lamGBS q ψ₀ χ k₀ r t j n c κ'.toLinearMap

end Loc

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem psiAt_sym {m2 : ℕ} (hc' : cOf R m2 = 1) (hc : cOf R (m2 + 1) = 0) (hs : cst.sharp = true) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (h : PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0) (i : Fin (R.N (m2 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) * y' i) ∧ redP P.1 ((qOf P.1 : X.E) * y' i) = if i.1 = R.k then 1 else 0 := by
  classical
  unfold PsiAt omPhi at h
  rw [ciOm_one] at h
  have h' := right_ne_zero_of_mul h
  unfold PhiAt at h'
  rw [if_pos hP, if_pos hs] at h'
  have hkr : R.k < R.r := by
    have := R.two_le_m
    unfold Ranks.r
    omega
  have hi : i.1 < R.N (m2 + 1) + cOf R (m2 + 1) := Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := Nat.cast_ne_zero.2 (qOf_pos P.1).ne'
  have a := phiGS_col (xqQ_mem P.1) hq0 _ _ hkr _ h' hi
  rw [symEntB_join_col _ hc' hc x₀ y' i.2] at a
  exact a

end Glob

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.JointLevelFrameZero
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColLevelXRest {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (piU : 𝓞 E)
    (e : A.vT ≃ {v : HeightOneSpectrum (𝓞 F) // ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal})
    (fz : ∀ (v : A.vT) (c : C.cls 0), Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → A.Fv v) where

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (t : Fin R.k → v.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL v L.Lb, ∀ a, (L.splitG i v h (x a)).1 = t a) ↔
      ∀ a, (((L.frG i v h)⁻¹ : GL (Fin R.k) (v.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F

  fM_pi : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal) (a : intV E v),
    (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (piU : E) →
    ∀ m : L.fM v h, a • m = 0

  fMe : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal), L.fM w h ≃+ A.Fv (e.symm ⟨w, h⟩)

  fv0 : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal) (c : C.cls 0)
    (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c))
    (t : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
    ((bc (prV (E := E) w) (L.y c : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] w.adicCompletion F)).mulVec t.1 =
      (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
    fz (e.symm ⟨w, h⟩) c z = fMe w h (L.fT w h t)

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) (O : AtTOwed a hS hH)

abbrev LevelZeroConditions : Type :=
  ∀ u : d.what₂.Word, ColLevelXRest ((hermCols a hS hP hK S hI).lev0 u) (d.piT u) ((hermCols a hS hP hK S hI).vT u)
    (fun v c z => ((d.colRec a).fm u).fv 0 v c ((hermAtT a hS hH O u).pr 0 v c z))

def levelZeroCompatibility (L0 : LevelZeroConditions a hS hH hP hK S hI O) :
    CH.Lev0Tied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := fun u =>
  { piG := d.piG
    piG_K := hH.piG_K
    piG_norm := fun i => by
      have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piG_norm i)
      rw [map_mul, map_natCast] at h
      exact h
    splitG_pi := S.sp_pi
    splitG_alg := S.sp_alg
    frG_lat := (L0 u).frG_lat
    fM_pi := (L0 u).fM_pi
    fMe := (L0 u).fMe
    fv0 := (L0 u).fv0 }

theorem piGConst (L0 : LevelZeroConditions a hS hH hP hK S hI O) :
    CH.PiGConst (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) (levelZeroCompatibility a hS hH hP hK S hI O L0) :=
  fun _ _ => rfl

theorem th_joint_sp (hCh : d.Ch.Ok) (u : d.what₂.Word) : (recGLoc a S hCh).sp = ((hermCols a hS hP hK S hI).lev0 u).splitG := rfl

theorem th_joint_piG (hCh : d.Ch.Ok) (L0 : LevelZeroConditions a hS hH hP hK S hI O) (u : d.what₂.Word) :
    (recGLoc a S hCh).piG = (levelZeroCompatibility a hS hH hP hK S hI O L0 u).piG := rfl

theorem jointLevel_frame_zero (hCh : d.Ch.Ok) (hl : d.lev = colLevS d.Ch) (u : d.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 d.host.F))
    (h : (d.host.g i : 𝓞 d.host.F) ∈ v.asIdeal) :
    (recGLev a S hCh hl hS hH hP u 0 (Nat.zero_le _)).fr i v h =
      Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R) _ (((hermCols a hS hP hK S hI).lev0 u).frG i v h) := by
  rw [recGLev_fr]
  have h0 : recUnit S u 0 i v h = 1 := by
    unfold recUnit
    rw [if_neg]
    have := d.R.two_le_m
    omega
  show glvD (d.R.N 0) v (recUnit S u 0 i v h) = _
  rw [h0, glvD_one]
  exact (map_one (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R) (v.adicCompletion d.host.F))).symm

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LevPackPSameCar
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hp_basePi_one (E : Type) [Field E] [NumberField E] [StarRing E] : BasePi (∅ : Finset (Pl E)) (1 : 𝓞 E) where
  dvd r := ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩
  cop := isCoprime_one_left

theorem hp_baseLb_empty (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) [NeZero n] :
    baseLb E n (∅ : Finset (Pl E)) = stdLat E n := by
  refine le_antisymm (rll_baseLb_le n ∅) fun x hx => ?_
  rw [rll_baseLb_eq n (hp_basePi_one E), rll_mem_dLat]
  rw [mem_stdLat] at hx
  refine ⟨fun i _ => hx i, ?_⟩
  rw [map_one, inv_one, one_mul]
  exact hx _

structure HCrdP (X : Fields) (n : ℕ) [NeZero n] {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  l0 : Submodule (𝓞 X.E) (Fin n' → X.E)
  hl0 : l0 = Formalism.L2.Forms.reL hn.symm (baseLb X.E n (∅ : Finset (Pl X.E)))
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPackP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (Lb : Submodule (𝓞 E) (Fin n → E)) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig J v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) → ((gp 1 : 𝓞 F) ∉ v.asIdeal) → Uloc v = levelVL hc.sig J v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v Lb, ∃ z ∈ Formalism.L2.Herm.locL v Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ Uloc v
  U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v
  cls : RecCls hc J Lb U stab lat

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)

def levPackP₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    LevPackP hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (baseLb X.E n (∅ : Finset (Pl X.E)))
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  Uloc := (tieLevP hc σ₀ Λ).Uloc
  Uloc_lev := (tieLevP hc σ₀ Λ).Uloc_lev
  Uloc_hyp := fun v h0 h1 => (tieLevP hc σ₀ Λ).Uloc_hyp v (fun hb => ((th_plUnder_vGs hc hPr v).1 hb).elim h0 h1)
    (fun h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n ∅ Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · rintro ⟨P, hP, _⟩
      exact absurd hP (Finset.notMem_empty P)
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  U := (tieLevP hc σ₀ Λ).U
  U_eq := (tieLevP hc σ₀ Λ).U_eq
  cls :=
    { y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
      y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
      y_lat := fun c x => by
        have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
        rw [xp_L_eq_N] at h
        exact h
      stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
      stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
      stabI_range := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range
      stabI_lat := fun c γ x => by
        have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_lat c γ x
        rw [xp_L_eq_N] at h
        exact h }

def levPackP (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) :
    LevPackP hc H.n' H.J Pr.g H.l0 (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPackP₁ hc hPr σ₀ Λ s hS hs

theorem levelPacking_sameCarrier (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    Formalism.L2.Forms.SameCar H.hn H.l0 (clsPG hc σ₀ Λ s hS hs Q).lev.Lb
      (levPackP hc hPr σ₀ Λ s hS hs H).Uloc (clsPG hc σ₀ Λ s hS hs Q).lev.Uloc
      (levPackP hc hPr σ₀ Λ s hS hs H).U (clsPG hc σ₀ Λ s hS hs Q).lev.U
      (fun c => ((levPackP hc hPr σ₀ Λ s hS hs H).cls.y c).1) (fun c => ((clsPG hc σ₀ Λ s hS hs Q).y c).1)
      (fun c t => ((levPackP hc hPr σ₀ Λ s hS hs H).cls.stabI c t).1)
      (fun c t => ((clsPG hc σ₀ Λ s hS hs Q).stabI c t).1) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_sameCar_refl _ _ _ _ _

theorem levelPacking_stabilizer (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) (c : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp)
    (t : MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) :
    Formalism.L2.Forms.reGL H.hn X.E ((levPackP hc hPr σ₀ Λ s hS hs H).cls.stabI c t).1 = ((ratEquiv hc n).symm t.1.1).1 := by
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact Formalism.L2.Forms.reGL_rfl _ _

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {Lb : Submodule (𝓞 E) (Fin S.rank → E)} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPackP.toStep (P : LevPackP hc S.rank S.gram gp Lb stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel0 hc S gp Lb where
  Uloc := P.Uloc
  Uloc_lev := P.Uloc_lev
  Uloc_hyp := P.Uloc_hyp
  Uloc_g := P.Uloc_g
  U := P.U
  U_eq := P.U_eq

def LevPackP.toCls (P : LevPackP hc S.rank S.gram gp Lb stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.QdfFrameRatio
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QFr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (Pl E)}

theorem qdf_frame_ratio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n)
    (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    ∀ y, (p'.fr P).symm (γ (p.fr P y)) ∈ stdAt E n P.1 ↔ y ∈ stdAt E n P.1 := by
  intro y
  have h1 := p'.2 P ((p'.fr P).symm (γ (p.fr P y)))
  have e1 : p'.1.2 P ((p'.fr P).symm (γ (p.fr P y))) = γ (p.fr P y) := LinearEquiv.apply_symm_apply _ _
  rw [e1] at h1
  rw [← h1]
  show γ (p.fr P y) ∈ localization₂ P.1.asIdeal p'.1.1.1.N ↔ _
  have hN' : p'.1.1.1.N = gmap γ p.1.1.1.N := hN
  rw [hN', mem_localization_gmap, LinearEquiv.symm_apply_apply]
  exact p.2 P y

def qdRatio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    GLint E n P.1 :=
  ⟨(p.fr P).trans (γ.trans (p'.fr P).symm), fun y => qdf_frame_ratio p p' γ hN P y⟩

end QFr

section QEmpty

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) {K : Type} [Field K]

def QLoc.empty (Θ : LevQFam E K n (∅ : Finset (Pl E))) : QLoc hc n ∅ Θ where
  sp P := absurd P.2 (Finset.notMem_empty _)
  sp_sig P := absurd P.2 (Finset.notMem_empty _)
  sp_alg P := absurd P.2 (Finset.notMem_empty _)
  sp_int P := absurd P.2 (Finset.notMem_empty _)
  sp_P P := absurd P.2 (Finset.notMem_empty _)
  U P := absurd P.2 (Finset.notMem_empty _)
  U_int P := absurd P.2 (Finset.notMem_empty _)
  U_rat P := absurd P.2 (Finset.notMem_empty _)
  U_dense P := absurd P.2 (Finset.notMem_empty _)
  chr P := absurd P.2 (Finset.notMem_empty _)
  chr_rat P := absurd P.2 (Finset.notMem_empty _)

end QEmpty

end Formalism.L2.Col
end
end

