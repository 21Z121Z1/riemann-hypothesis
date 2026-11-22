import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0228
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0229
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0231
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0233
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrd
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdE

open TVCrdAlg TVCrdLoc TVCrdGerm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem memW {f : (Fin r → ℂ) → X} (h : f ∈ WSm r X) :
    ContDiffOn ℝ ∞ f (OmX r) ∧ ∀ x, x ∉ OmX r → f x = 0 := h

def opE (l : Fin r) (i : Fin 6) : Module.End ℂ (WSm r X) where
  toFun f := ⟨opL l i f, preserved_operators_holds r X l i f f.2⟩
  map_add' f g := Subtype.ext (linear_operators_holds r X l i f g 1 f.2 g.2).1
  map_smul' a f := Subtype.ext (linear_operators_holds r X l i f f a f.2 f.2).2

@[simp] theorem opE_coe (l : Fin r) (i : Fin 6) (f : WSm r X) :
    ((opE l i f : WSm r X) : (Fin r → ℂ) → X) = opL l i f := rfl

theorem opL_three (l : Fin r) : opL (E := X) l 3 = pbOp l := rfl
theorem opL_four (l : Fin r) : opL (E := X) l 4 = cbOp l := rfl
theorem opL_five (l : Fin r) : opL (E := X) l 5 = cbiOp l := rfl

def mulE (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) : Module.End ℂ (WSm r X) where
  toFun f := ⟨fun x => a x • (f : (Fin r → ℂ) → X) x,
    ⟨ha.smul (memW f.2).1, fun x hx => by simp [(memW f.2).2 x hx]⟩⟩
  map_add' f g := Subtype.ext (funext fun x => by simp [smul_add])
  map_smul' s f := Subtype.ext (funext fun x => by simp [smul_comm (a x) s])

@[simp] theorem mulE_coe (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) (f : WSm r X) :
    ((mulE a ha f : WSm r X) : (Fin r → ℂ) → X) = fun x => a x • (f : (Fin r → ℂ) → X) x := rfl

theorem comm_of_mul (A B : Module.End ℂ (WSm r X)) (a b : (Fin r → ℂ) → ℂ)
    (hA : ∀ (f : WSm r X) x, (A f : (Fin r → ℂ) → X) x = a x • (f : (Fin r → ℂ) → X) x)
    (hB : ∀ (f : WSm r X) x, (B f : (Fin r → ℂ) → X) x = b x • (f : (Fin r → ℂ) → X) x) : Commute A B := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
  show (A (B f) : (Fin r → ℂ) → X) x = (B (A f) : (Fin r → ℂ) → X) x
  rw [hA, hB, hB, hA, smul_smul, smul_smul, mul_comm]

def PN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 3 else 0
def CbN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 4 else 0
def CbiN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 5 else 0

theorem PN_coe (i : ℕ) (f : WSm r X) : ((PN r X i f : WSm r X) : (Fin r → ℂ) → X) = pbN r i f := by
  unfold PN pbN; split_ifs <;> rfl
theorem CbN_coe (i : ℕ) (f : WSm r X) : ((CbN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbN r i f := by
  unfold CbN cbN; split_ifs <;> rfl
theorem CbiN_coe (i : ℕ) (f : WSm r X) : ((CbiN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbiN r i f := by
  unfold CbiN cbiN; split_ifs <;> rfl

theorem CbN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbN r X i f : (Fin r → ℂ) → X) x = (if h : i < r then star (x ⟨i, h⟩) else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbN; split_ifs <;> simp [opL, cbOp]
theorem CbiN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbiN r X i f : (Fin r → ℂ) → X) x =
      (if h : i < r then (star (x ⟨i, h⟩))⁻¹ else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbiN; split_ifs <;> simp [opL, cbiOp]

theorem comm_PN_CbN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbN r X j) := by
  unfold PN CbN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 4 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp
theorem comm_PN_CbiN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbiN r X j) := by
  unfold PN CbiN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 5 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp

theorem comm_CbN_CbN (i j : ℕ) : Commute (CbN r X i) (CbN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbN_mul j)
theorem comm_CbN_CbiN (i j : ℕ) : Commute (CbN r X i) (CbiN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbiN_mul j)
theorem comm_CbiN_CbiN (i j : ℕ) : Commute (CbiN r X i) (CbiN r X j) :=
  comm_of_mul _ _ _ _ (CbiN_mul i) (CbiN_mul j)

def Gop (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] : Module.End ℂ (WSm r X) :=
  mulE (gaugeF k r) gaugeF_smooth

theorem comm_G_CbN (k i : ℕ) : Commute (Gop k r X) (CbN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbN_mul i)
theorem comm_G_CbiN (k i : ℕ) : Commute (Gop k r X) (CbiN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbiN_mul i)

def sG (k r : ℕ) (i : Fin r) : ℂ := ((Mdim k r i - 1 : ℕ) : ℂ) / 2

theorem P_G (k : ℕ) (i : Fin r) : opE i 3 * Gop k r X = Gop k r X * opE i 3 + sG k r i • Gop k r X := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  show pbOp i (fun x => gaugeF k r x • (f : (Fin r → ℂ) → X) x) = _
  rw [pbOp_gauge i _ f.2]
  funext x
  simp [Gop, opL_three, sG]

theorem G_PN (k : ℕ) {i : ℕ} (hi : i < r) :
    Gop k r X * PN r X i = (PN r X i - sG k r ⟨i, hi⟩ • 1) * Gop k r X := by
  have h := P_G (X := X) k ⟨i, hi⟩
  have hP : PN r X i = opE ⟨i, hi⟩ 3 := dif_pos hi
  rw [hP, sub_mul, smul_mul_assoc, one_mul, h]
  abel

def Dd (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (j : ℕ) : Module.End ℂ (WSm r X) :=
  y • 1 - PN r X j
def Ee (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (j : ℕ) : Module.End ℂ (WSm r X) :=
  CbN r X j * CbiN r X (j - 1)
def Dw (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (w : ℂ) (m : ℕ) : Module.End ℂ (WSm r X) :=
  (w - (m : ℂ)) • 1 - PN r X (r - m - 1)

theorem hDe (y : ℂ) : ∀ i j, i + 1 ≤ j → Dd r X y j * Ee r X i = Ee r X i * Dd r X y j := by
  intro i j hij
  have : Commute (Dd r X y j) (Ee r X i) := by
    unfold Dd Ee
    refine Commute.sub_left ((Commute.one_left _).smul_left y) ?_
    exact (comm_PN_CbN (by omega)).mul_right (comm_PN_CbiN (by omega))
  exact this.eq

theorem hee : ∀ i j, Ee r X i * Ee r X j = Ee r X j * Ee r X i := by
  intro i j
  have : Commute (Ee r X i) (Ee r X j) := by
    unfold Ee
    refine Commute.mul_left ?_ ?_
    · exact (comm_CbN_CbN i j).mul_right (comm_CbN_CbiN i (j - 1))
    · exact ((comm_CbN_CbiN j (i - 1)).symm).mul_right (comm_CbiN_CbiN (i - 1) (j - 1))
  exact this.eq

theorem hGe (k : ℕ) : ∀ j, Gop k r X * Ee r X j = Ee r X j * Gop k r X := by
  intro j
  exact ((comm_G_CbN k j).mul_right (comm_G_CbiN k (j - 1))).eq

theorem shift_eq (k : ℕ) (y : ℂ) {m : ℕ} (hm : m < r) :
    kvTop k r y - (m : ℂ) + sG k r ⟨r - m - 1, by omega⟩ = y := by
  have h : Mdim k r ⟨r - m - 1, by omega⟩ - 1 = 2 * m + k + 2 := by
    simp only [Mdim]; omega
  simp only [sG, kvTop, h]
  push_cast
  ring

theorem hG (k : ℕ) (y : ℂ) : ∀ m < r,
    Gop k r X * Dw r X (kvTop k r y) m = Dd r X y (r - m - 1) * Gop k r X := by
  intro m hm
  unfold Dw Dd
  rw [mul_sub, mul_smul_comm, mul_one, G_PN k (show r - m - 1 < r by omega), sub_mul, sub_mul, smul_mul_assoc,
    smul_mul_assoc, one_mul]
  have hy := shift_eq (r := r) k y hm
  conv_rhs => rw [← hy]
  rw [add_smul]
  abel

theorem iteratedOperator_coe (w : ℂ) : ∀ (m : ℕ) (f : WSm r X),
    (kvP r w m).1 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).1 f : WSm r X) ∧
      (kvP r w m).2 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).2 f : WSm r X)
  | 0, f => ⟨rfl, rfl⟩
  | m + 1, f => by
    have hD : (fun c => (w - (m : ℂ)) • (f : (Fin r → ℂ) → X) c - pbN r (r - m - 1) (f : (Fin r → ℂ) → X) c) =
        ((Dw r X w m f : WSm r X) : (Fin r → ℂ) → X) := by
      funext c
      simp [Dw, PN_coe]
    refine ⟨?_, (iteratedOperator_coe w m f).1⟩
    simp only [kvP, topK]
    rw [hD, (iteratedOperator_coe w m _).1, (iteratedOperator_coe w m f).2, ← CbiN_coe, ← CbN_coe]
    simp [Ee]

theorem vABm_coe (y : ℂ) : ∀ (i : ℕ) (f : WSm r X),
    (vABm r y i).1 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).1 f : WSm r X) ∧
      (vABm r y i).2 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).2 f : WSm r X)
  | 0, f => ⟨rfl, rfl⟩
  | i + 1, f => by
    by_cases h : i < r
    · obtain ⟨h1, h2⟩ := vABm_coe y i f
      have hP : PN r X i = opE ⟨i, h⟩ 3 := dif_pos h
      have hC : CbN r X i = opE ⟨i, h⟩ 4 := dif_pos h
      have hCi : CbiN r X i = opE ⟨i, h⟩ 5 := dif_pos h
      simp only [vABm, dif_pos h, botA, if_pos h]
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · simp [Dd, hP, hC, opL_three, opL_four]
      · simp [hCi, opL_five]
    · simp only [vABm, dif_neg h, botA, if_neg h]
      exact vABm_coe y i f

end Formalism.FourierDecayAlt.P.CutMP.TVCrdE

namespace Formalism.FourierDecayAlt.P.CutMP

open TVCrdAlg TVCrdLoc TVCrdGerm TVCrdE

theorem toda_coordinate_holds : TVCrd := by
  intro k r X _ _ y Φ U c hU hUO hc hΨ
  obtain ⟨φ, hφ, hΦ, hΨφ⟩ := TVCrdLoc.loc (k := k) Φ U c hU hUO hc hΨ
  have eL : kvC r (kvTop k r y) r Φ c = kvC r (kvTop k r y) r φ c :=
    (iteratedOperator_germ (kvTop k r y) r Φ φ c hΦ).1.eq_of_nhds
  have eR : (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c =
      (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') c :=
    (vABm_germ y r _ _ c hΨφ).1.eq_of_nhds
  rw [eL, eR]
  let f : WSm r X := ⟨φ, hφ⟩
  have hK : kvC r (kvTop k r y) r φ = ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f : WSm r X) :=
    (iteratedOperator_coe (kvTop k r y) r f).1
  have hA : (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') =
      ((botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 (Gop k r X f) : WSm r X) :=
    (vABm_coe y r (Gop k r X f)).1
  have hB := (botA_eq (Dd r X y) (CbN r X) (CbiN r X) r r le_rfl).1
  have hT := (topK_eq (Dd r X y) (Ee r X) (hDe y) hee r (fun m => Dd r X y (r - m - 1)) (fun _ _ => rfl) r le_rfl).1
  have hC := (topK_conj (Gop k r X) (Dw r X (kvTop k r y)) (fun m => Dd r X y (r - m - 1)) (Ee r X) r
    (hG k y) (hGe k) r le_rfl).1
  rw [Nat.sub_self] at hT
  have hAT : (botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 =
      (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 := by
    rw [hB, hT]; rfl
  rw [hK, hA, hAT]
  have h2 : (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 (Gop k r X f) =
      Gop k r X ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f) := by
    rw [← Module.End.mul_apply, ← hC, Module.End.mul_apply]
  rw [h2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHAsm
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fsv_zero' (t : ℂ) : fsv 0 t = 1 := by simp [fsv]

theorem fsv_mul' (s s' t : ℂ) : fsv s t * fsv s' t = fsv (s + s') t := by
  unfold fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add]
  ring

theorem fsv_contDiff' (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hc : ContDiff ℝ ∞ (fun t : ℂ => conj t) := Complex.conjCLE.contDiff
  have h1 : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul hc)
  have he : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
  exact he.comp h1

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem cc_zero {P : M.Par} (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc j hj t c ⟨0, by omega⟩ = t := by
  simp [cc, consC]

theorem vw_entry (hU : UUiwScalar) {V : Type} [AddCommGroup V] [Module ℂ V] (S : Type) [Fintype S] [DecidableEq S]
    (Wv Wv' : Module.End ℂ V) (s : ℂ) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S) :
    ∃ lam : ℂ, ∀ Φ : V, (Wd.Vw (mkP Wv Wv') s w a b).1 Φ = lam • Wv Φ := by
  obtain ⟨lam, hlam⟩ := Algebra.mem_bot.1 (hU (Pr V) S s w a b)
  refine ⟨lam, fun Φ => ?_⟩
  have hab : Wd.Vw (mkP Wv Wv') s w a b = mkP Wv Wv' * Wd.UUiw (A := Pr V) s w a b := by
    simp [Wd.Vw, Wd.io, Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [hab, ← hlam]
  change (Wv * algebraMap ℂ (Module.End ℂ V) lam) Φ = _
  rw [Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]

theorem class0_form (hU : UUiwScalar) (S : Type) [Fintype S] [DecidableEq S] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
    (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (l0 : ℕ) :
    ∀ (i : Fin ((JC.parLev P j).r + 1))
      (Ψ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) i Ψ → i = 0 →
      ∃ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
        (Φ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (s κ : ℂ),
        JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F ∧
        IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ ∧
        ∀ c g, (Ψ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g =
          (κ * fsv s (c ⟨0, by change 0 < P.r - j; omega⟩)) •
            (Φ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g := by
  intro i Ψ h
  induction h with
  | jf F Φ hF hΦ =>
    intro _
    exact ⟨F, Φ, 0, 1, hF, hΦ, fun c g => by simp [fsv_zero']⟩
  | slice l w a b Φ hw hΦ ih =>
    intro h
    exact absurd h (Fin.succ_ne_zero l)
  | waveC l w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have hl0 : l.val = 0 := by
      have := congrArg Fin.val h
      simpa using this
    obtain ⟨F, Φ0, s0, κ0, hF, hΦ0, hv⟩ := ih h
    obtain ⟨lam, hlam⟩ := vw_entry hU S Wv Wv' s w a b
    refine ⟨F, Φ0, s + s0, lam * κ0, hF, hΦ0, fun c g => ?_⟩
    have hcl : c l = c ⟨0, by change 0 < P.r - j; omega⟩ := congrArg c (Fin.ext hl0)
    rw [hlam, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hW, hv, smul_smul, smul_smul]
    beta_reduce
    rw [hcl, ← fsv_mul']
    congr 1
    ring
  | waveZ w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have := congrArg Fin.val h
    simp [JC.parLev] at this
    omega

variable {P : M.Par} {T : D.LevTower P.k P.r Wp Wq} {j : ℕ} {hj : j + 1 ≤ P.r}

theorem inC_add (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (h' : InC T j hj Ψ') : InC T j hj (Ψ + Ψ') := by
  obtain ⟨G, hG, hR⟩ := h
  obtain ⟨G', hG', hR'⟩ := h'
  refine ⟨fun t γ => G t γ + G' t γ, (h2 Wp Wq P T j G G' hG hG' (fun _ => 1) contDiffOn_const).1,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hR t ht x hx, hR' t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G' hG hG' t ht 0 x hx).1]

theorem inC_smul (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (a : ℂ) : InC T j hj (a • Ψ) := by
  obtain ⟨G, hG, hR⟩ := h
  refine ⟨fun t γ => a • G t γ, (h2 Wp Wq P T j G G hG hG (fun _ => a) contDiffOn_const).2,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hR t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht a x hx).2]

theorem inC_seed (h6 : CellTie) (h7 : SliceFamGood) (h8 : SliceFamJF)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hF : JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F)
    (Φ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ) :
    InC T j hj Φ := by
  refine ⟨sliceFam T j hj F, h7 Wp Wq P T hP hT j hj hPj hPs F hF, fun t ht x hx => ?_⟩
  obtain ⟨hdom, hGV, hOm⟩ := h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx
  have e1 : (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - j) (Fin.last _) (B.JF (T.bs j) F) (cc j hj t x.1) (gi j hj x.2) :=
    hΦ (cc j hj t x.1, gi j hj x.2) hdom
  have e2 := Formalism.FourierDecayAlt.P.PBP.resG_cast (k := P.k) (ρ := P.r - (j + 1)) (n := P.r - j) (by omega) ht
    (B.JF (T.bs j) F) x.1 x.2
  rw [e1]
  refine e2.trans ?_
  unfold resG
  rw [h8 Wp Wq P T hP hT j hj hPj hPs F hF t ht _ hGV hOm, smul_comm]
  congr 2

theorem inC_wave (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Φ Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'} (s κ : ℂ)
    (hv : ∀ c g, (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g =
      (κ * fsv s (c ⟨0, by omega⟩)) • (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g)
    (h : InC T j hj Φ) : InC T j hj Ψ := by
  obtain ⟨G, hG, hR⟩ := h
  have hm : ContDiffOn ℝ ∞ (fun t : ℂ => κ * fsv s t) {t | t ≠ 0} :=
    (contDiff_const.mul (fsv_contDiff' s)).contDiffOn
  refine ⟨fun t γ => (κ * fsv s t) • G t γ, (h2 Wp Wq P T j G G hG hG _ hm).2, fun t ht x hx => ?_⟩
  rw [hv, cc_zero, hR t ht x hx, (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht _ x hx).2]

theorem inC_adjoin (h2 : FamAlg) (h4 : RepLin) (h9 : OpClosed)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (X.op ⟨0, by omega⟩))) :
    ∀ Ψ, InC T j hj Ψ → InC T j hj (A Ψ) := by
  induction hA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact fun Ψ h => h9 Wp Wq P T hP hT j hj hPj hPs X i Ψ h
  | algebraMap r =>
    intro Ψ h
    rw [Module.algebraMap_end_apply]
    exact inC_smul h2 h4 hP hT hPs h r
  | add x y _ _ hx hy =>
    intro Ψ h
    rw [LinearMap.add_apply]
    exact inC_add h2 h4 hP hT hPs (hx Ψ h) (hy Ψ h)
  | mul x y _ _ hx hy =>
    intro Ψ h
    rw [Module.End.mul_apply]
    exact hx _ (hy Ψ h)

theorem herKc_jf' {S : Type} [Fintype S] [DecidableEq S] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
    {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
    {D : B.RealPlaceData P.k P.r Wp Wq} (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

theorem span_step
    (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
      RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (K : Submodule ℂ (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'))
    (s : Set (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (hgen : ∀ Ψ ∈ s, Tt (A Ψ) ∈ K) :
    ∀ Ψ ∈ Submodule.span ℂ s, Tt (A Ψ) ∈ K := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact K.add_mem hx hy
  | smul r x _ hx => rw [map_smul, map_smul]; exact K.smul_mem r hx

end asm

theorem sliceStepHer_of (h1 : FamJFOK) (h2 : FamAlg) (h4 : RepLin) (h6 : CellTie) (h7 : SliceFamGood)
    (h8 : SliceFamJF) (h9 : OpClosed) (h10 : BTlAdjoin) (h11 : UUiwScalar) : PTie.SliceStepHer := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj l0 _ _ Xj μj Lj stj Xs μs Ls sts hDj hDs Tt t ht hTt S _ _ w a b hw Ψ hΨ
  have hPj := hDj.1
  have hPs := hDs.1
  have hAct := hDj.2.2.1
  have hA := h10 Wp Wq P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj Lj hAct S
    ⟨0, by change 0 < P.r - j; omega⟩ w a b
  have hΨ' : Ψ ∈ Submodule.span ℂ
      {Φ | HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0 Φ} := hΨ
  refine span_step (P := P) (T := T) (j := j) Tt (bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1
    (herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
      l0 (T.bs (j + 1)) 0) _ (fun Ψ hg => ?_) Ψ hΨ'
  obtain ⟨F, Φ, s, κ, hF, hΦ, hv⟩ := class0_form h11 S P T j hj Lj stj l0 0 Ψ hg rfl
  have hC0 : InC T j hj Φ := inC_seed h6 h7 h8 hP hT hPj hPs F hF Φ hΦ
  have hC : InC T j hj Ψ := inC_wave (Φ := Φ) h2 h4 hP hT hPs s κ hv hC0
  obtain ⟨G, hG, hR⟩ := inC_adjoin h2 h4 h9 hP hT hPj hPs Xj _ hA Ψ hC
  have hJ := h1 Wp Wq P T j G hG t ht
  have hRad : IsRadJF (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'
      (T.bs (j + 1)) (G t) (Tt ((bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1 Ψ)) := fun x hx =>
    (hTt _ x.1 x.2).trans (hR t ht x hx)
  exact herKc_jf' (S := S) (P := JC.parLev P (j + 1)) (L := Ls) (st := sts) (l0 := l0) (G t) hJ _ hRad

end Formalism.FourierDecayAlt.P.CutSH

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfHeads : Prop := KB.RadHead → KB.HeadTop → KB.PStd

theorem pStdOfHeads : PStdOfHeads := fun hRH hHT =>
  pStdOfParts hRH hHT Formalism.FourierDecayAlt.P.module_form_eq_radial_form_one Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar

theorem pStdCpt_of_heads (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_cpt_of_parts hP hRH hHT Formalism.FourierDecayAlt.P.module_form_eq_radial_form_one Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.standard_pairing_of_heads : Formalism.FourierDecayAlt.P.PBO.PStdOfHeads := Formalism.FourierDecayAlt.P.PBO.pStdOfHeads
end
end

