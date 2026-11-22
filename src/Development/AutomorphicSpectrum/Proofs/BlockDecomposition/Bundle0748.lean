import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.HighestCone

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}

theorem letter_comm (hg : Formalism.REAL.GlRel K) (a b c d : Fin n) (v : V) :
    K a b (K c d v) = K c d (K a b v) + (if b = c then K a d v else 0)
      - (if d = a then K c b v else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) (hg a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h3 : (if b = c then K a d else 0 : Module.End ℂ V) v = if b = c then K a d v else 0 := by
    split_ifs <;> simp
  have h4 : (if d = a then K c b else 0 : Module.End ℂ V) v = if d = a then K c b v else 0 := by
    split_ifs <;> simp
  rw [h3, h4] at h
  rw [add_sub_assoc, ← h]
  abel

theorem levi_step (hg : Formalism.REAL.GlRel K) (lev : Fin n → ℕ) (C : Fin n → Fin n → Prop)
    (Y Z : Submodule ℂ V)
    (hmin : ∀ S : Submodule ℂ V, Y ≤ S →
      (∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S) → Z ≤ S)
    (hZ : ∀ a b, lev a = lev b → ∀ v ∈ Z, K a b v ∈ Z) (hYZ : Y ≤ Z)
    (hC : ∀ a b c d, C a b → lev c = lev d → (b = c → C a d) ∧ (d = a → C c b))
    (hY : ∀ a b, C a b → ∀ y ∈ Y, K a b y ∈ Z) :
    ∀ a b, C a b → ∀ z ∈ Z, K a b z ∈ Z := by
  let S : Submodule ℂ V :=
    { carrier := {z | z ∈ Z ∧ ∀ a b, C a b → K a b z ∈ Z}
      add_mem' := fun {u w} hu hw => ⟨Z.add_mem hu.1 hw.1, fun a b h => by
        rw [map_add]; exact Z.add_mem (hu.2 a b h) (hw.2 a b h)⟩
      zero_mem' := ⟨Z.zero_mem, fun a b _ => by rw [map_zero]; exact Z.zero_mem⟩
      smul_mem' := fun r u hu => ⟨Z.smul_mem r hu.1, fun a b h => by
        rw [map_smul]; exact Z.smul_mem r (hu.2 a b h)⟩ }
  have hle : Z ≤ S := by
    refine hmin S (fun y hy => ⟨hYZ hy, fun a b h => hY a b h y hy⟩) ?_
    intro c d hcd v hv
    refine ⟨hZ c d hcd v hv.1, fun a b hab => ?_⟩
    rw [letter_comm hg a b c d v]
    refine Z.sub_mem (Z.add_mem (hZ c d hcd _ (hv.2 a b hab)) ?_) ?_
    · split_ifs with h
      · exact hv.2 a d ((hC a b c d hab hcd).1 h)
      · exact Z.zero_mem
    · split_ifs with h
      · exact hv.2 c b ((hC a b c d hab hcd).2 h)
      · exact Z.zero_mem
  intro a b hab z hz
  exact (hle hz).2 a b hab

def shift (c : Fin n → Fin n → ℕ) (t : Fin n) : ℝ :=
  ∑ a, ∑ b, (c a b : ℝ) * ((if t = a then 1 else 0) - (if t = b then 1 else 0))

theorem shift_add (c : Fin n → Fin n → ℕ) (a b t : Fin n) :
    shift (fun p q => c p q + if p = a ∧ q = b then 1 else 0) t =
      shift c t + ((if t = a then 1 else 0) - (if t = b then 1 else 0)) := by
  unfold shift
  have : ∀ p q : Fin n, (((c p q + if p = a ∧ q = b then 1 else 0 : ℕ) : ℝ)) *
      ((if t = p then 1 else 0) - (if t = q then 1 else 0)) =
      (c p q : ℝ) * ((if t = p then 1 else 0) - (if t = q then 1 else 0)) +
      (if p = a then (if q = b then ((if t = p then (1:ℝ) else 0) - (if t = q then 1 else 0)) else 0) else 0) := by
    intro p q
    by_cases hp : p = a <;> by_cases hq : q = b <;> simp [hp, hq]
    ring
  simp only [this, Finset.sum_add_distrib]
  simp

theorem weight_letter (hg : Formalism.REAL.GlRel K) (a b t : Fin n) (τ : ℂ) (y : V)
    (ht : K t t y = τ • y) :
    K t t (K a b y) = (τ + (((if t = a then 1 else 0) - (if t = b then 1 else 0) : ℝ) : ℂ)) • K a b y := by
  rw [letter_comm hg t t a b y, ht, map_smul]
  by_cases h1 : t = a <;> by_cases h2 : t = b
  · subst h1; subst h2; simp
  · subst h1
    have h2' : ¬ b = t := fun h => h2 h.symm
    simp [h2', h2, add_smul]
  · subst h2
    simp [h1, add_smul, sub_eq_add_neg]
  · have h2' : ¬ b = t := fun h => h2 h.symm
    simp [h1, h2, h2']

def coneSpan (K : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (ν : Fin n → ℝ) :
    Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → lev b < lev a) ∧
    ∀ t, K t t y = (((ν t + shift c t : ℝ)) : ℂ) • y}

theorem coneSpan_letter (hg : Formalism.REAL.GlRel K) (lev : Fin n → ℕ) (ν : Fin n → ℝ) (a b : Fin n)
    (hab : lev b < lev a) (v : V) (hv : v ∈ coneSpan K lev ν) : K a b v ∈ coneSpan K lev ν := by
  unfold coneSpan at hv ⊢
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, hy⟩ := hy
    refine Submodule.subset_span ⟨fun p q => c p q + if p = a ∧ q = b then 1 else 0, ?_, ?_⟩
    · intro p q hpq
      by_cases h : p = a ∧ q = b
      · rw [h.1, h.2]; exact hab
      · apply hc p q
        simpa [h] using hpq
    · intro t
      rw [weight_letter hg a b t _ y (hy t), shift_add]
      congr 1
      push_cast
      ring
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu

theorem inCone_of_ne (lev : Fin n → ℕ) (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ)
    (hev : ∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b, c a b ≠ 0 → lev b < lev a) (y : V)
    (hy : ∀ t, K t t y = (((ν t + shift c t : ℝ)) : ℂ) • y) (hne : ev y ≠ 0) :
    inCone lev (ν - μ) := by
  have hμ : ∀ t, μ t = ν t + shift c t := by
    intro t
    have h := hev t y
    rw [hy t, map_smul, smul_eq_mul] at h
    have := mul_right_cancel₀ hne h
    exact_mod_cast this.symm
  refine ⟨fun a b => c b a, fun a b h => hc b a h, fun x => ?_⟩
  rw [Pi.sub_apply, hμ x]
  have hs : shift c x = ∑ a, ∑ b, (c b a : ℝ) * ((if x = b then 1 else 0) - (if x = a then 1 else 0)) := by
    unfold shift
    rw [Finset.sum_comm]
  rw [hs, sub_add_cancel_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem inCone_of_highest : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V), Formalism.REAL.KHighest (fun _ => true) K ν x → (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) → (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) → (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) → inCone lev (ν - μ) := by
  intro n V _ _ K hg lev hlev ev μ ν x hx hoff hdiag ⟨T, hT, hTx⟩

  let Y : Submodule ℂ V := sInf {S | x ∈ S ∧ ∀ a b, lev b < lev a → ∀ v ∈ S, K a b v ∈ S}
  let Z : Submodule ℂ V := sInf {S | Y ≤ S ∧ ∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S}
  have hxY : x ∈ Y := by
    refine (Submodule.mem_sInf).2 fun S hS => hS.1
  have hYl : ∀ a b, lev b < lev a → ∀ v ∈ Y, K a b v ∈ Y := by
    intro a b hab v hv
    refine (Submodule.mem_sInf).2 fun S hS => hS.2 a b hab v ((Submodule.mem_sInf).1 hv S hS)
  have hYmin : ∀ S : Submodule ℂ V, x ∈ S →
      (∀ a b, lev b < lev a → ∀ v ∈ S, K a b v ∈ S) → Y ≤ S :=
    fun S h1 h2 => sInf_le ⟨h1, h2⟩
  have hYZ : Y ≤ Z := le_sInf fun S hS => hS.1
  have hZl : ∀ a b, lev a = lev b → ∀ v ∈ Z, K a b v ∈ Z := by
    intro a b hab v hv
    refine (Submodule.mem_sInf).2 fun S hS => hS.2 a b hab v ((Submodule.mem_sInf).1 hv S hS)
  have hZmin : ∀ S : Submodule ℂ V, Y ≤ S →
      (∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S) → Z ≤ S :=
    fun S h1 h2 => sInf_le ⟨h1, h2⟩

  have step1 : ∀ a b, lev b < lev a → ∀ z ∈ Z, K a b z ∈ Z := by
    refine levi_step hg lev (fun a b => lev b < lev a) Y Z hZmin hZl hYZ ?_ ?_
    · intro a b c d hab hcd
      constructor
      · rintro rfl; show lev d < lev a; omega
      · rintro rfl; show lev b < lev c; omega
    · intro a b hab y hy
      exact hYZ (hYl a b hab y hy)

  have step2 : ∀ a b, ∀ y ∈ Y, K a b y ∈ Z := by
    let S : Submodule ℂ V :=
      { carrier := {y | y ∈ Y ∧ ∀ a b, K a b y ∈ Z}
        add_mem' := fun {u w} hu hw => ⟨Y.add_mem hu.1 hw.1, fun a b => by
          rw [map_add]; exact Z.add_mem (hu.2 a b) (hw.2 a b)⟩
        zero_mem' := ⟨Y.zero_mem, fun a b => by rw [map_zero]; exact Z.zero_mem⟩
        smul_mem' := fun r u hu => ⟨Y.smul_mem r hu.1, fun a b => by
          rw [map_smul]; exact Z.smul_mem r (hu.2 a b)⟩ }
    have hle : Y ≤ S := by
      refine hYmin S ⟨hxY, fun a b => ?_⟩ ?_
      · rcases lt_trichotomy (lev a) (lev b) with h | h | h
        · have hab : a < b := by
            by_contra hn
            have := hlev (not_lt.1 hn)
            omega
          rw [hx.2 a b hab rfl]
          exact Z.zero_mem
        · exact hZl a b h x (hYZ hxY)
        · exact hYZ (hYl a b h x hxY)
      · intro c d hcd v hv
        refine ⟨hYl c d hcd v hv.1, fun a b => ?_⟩
        rw [letter_comm hg a b c d v]
        refine Z.sub_mem (Z.add_mem (step1 c d hcd _ (hv.2 a b)) ?_) ?_
        · split_ifs
          · exact hv.2 a d
          · exact Z.zero_mem
        · split_ifs
          · exact hv.2 c b
          · exact Z.zero_mem
    intro a b y hy
    exact (hle hy).2 a b

  have step3 : ∀ a b, ∀ z ∈ Z, K a b z ∈ Z := by
    intro a b
    exact levi_step hg lev (fun _ _ => True) Y Z hZmin hZl hYZ
      (fun _ _ _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩)
      (fun a b _ y hy => step2 a b y hy) a b trivial

  have hadj : ∀ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ∀ z ∈ Z, T z ∈ Z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem A hA =>
      obtain ⟨a, b, rfl⟩ := hA
      exact step3 a b
    | algebraMap r =>
      intro z hz
      simpa [Module.algebraMap_end_apply] using Z.smul_mem r hz
    | add A B _ _ hA hB =>
      intro z hz
      exact Z.add_mem (hA z hz) (hB z hz)
    | mul A B _ _ hA hB =>
      intro z hz
      exact hA _ (hB z hz)
  by_contra hcone

  have hY0 : Y ≤ LinearMap.ker ev := by
    have h1 : Y ≤ coneSpan K lev ν := by
      refine hYmin _ (Submodule.subset_span ⟨fun _ _ => 0, by simp, fun t => ?_⟩)
        (fun a b hab v hv => coneSpan_letter hg lev ν a b hab v hv)
      simpa [shift] using hx.1 t
    refine h1.trans ?_
    refine Submodule.span_le.2 ?_
    rintro y ⟨c, hc, hy⟩
    by_contra hne
    exact hcone (inCone_of_ne lev ev μ ν hdiag c hc y hy hne)
  have hZ0 : Z ≤ LinearMap.ker ev := by
    refine hZmin _ hY0 ?_
    intro a b _ v hv
    rw [LinearMap.mem_ker] at hv ⊢
    by_cases hab : a = b
    · subst hab
      rw [hdiag, hv, mul_zero]
    · exact hoff a b v ‹_› hab
  exact hTx (hZ0 (hadj T hT x (hYZ hxY)))

end GlobalTheory.CompanionTheory.HighestCone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariant
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.FMul

open GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem ini_injective (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective _

theorem rows_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    (p * g).submatrix (ini j) id = p.submatrix (ini j) (ini j) * g.submatrix (ini j) id := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)
  intro k hk
  have hjk : j < k := by
    by_contra h
    have h' : (k : ℕ) ≤ j := by
      have := not_lt.1 h
      exact Fin.le_def.1 this
    exact hk ⟨⟨k, by omega⟩, by ext; rfl⟩
  have haj : ini j a ≤ j := by
    have := a.isLt
    rw [Fin.le_def]
    show (a : ℕ) ≤ j
    omega
  rw [hz _ _ haj hjk, zero_mul]

theorem lm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    lm j (p * g) = lm j p * lm j g := by
  have h : (p * g).submatrix (ini j) (ini j) =
      p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j) := by
    ext a c
    exact congrFun (congrFun (rows_mul j p g hz) a) (ini j c)
  rw [lm, h, Matrix.det_mul, lm, lm]

theorem gm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j (p * g) = lm j p * star (lm j p) * gm j g := by
  rw [gm, rows_mul j p g hz, Matrix.conjTranspose_mul]
  have h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id *
      ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) =
      p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) *
        (p.submatrix (ini j) (ini j))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, lm, gm]
  ring

theorem gm_one (j : Fin n) : gm j (1 : Mat n) = 1 := by
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one _ (ini_injective j)]
  rw [gm, h, Matrix.det_one]

theorem gm_left (j : Fin n) (p : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j p = lm j p * star (lm j p) := by
  have := gm_mul j p 1 hz
  rwa [Matrix.mul_one, gm_one, mul_one] at this

theorem dif_eq_zero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  obtain ⟨-, hl⟩ := hl
  have hlam := hl _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    simp only [muZ, hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    simp only [yZ, hlam, hmu]
  constructor
  · simp only [dif, dif_pos h, hmu, sub_self]
  · simp only [dif, dif_pos h, hy, sub_self]

theorem fRaw_mul : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  intro n lam _ lev hl p hp g hg
  obtain ⟨hp1, hp2⟩ := hp
  have hpg : p * g ∈ GLs n := by
    show (p * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hp1 hg
  simp only [fRaw, Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b
  · have hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0 := fun a b h1 h2 => hp2 a b (hgood a b h1 h2)
    rw [lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · push_neg at hgood
    obtain ⟨a, b, haj, hjb, hba⟩ := hgood
    have hmono := hl.1
    have hb : (j : ℕ) < b := Fin.lt_def.1 hjb
    have h : (j : ℕ) + 1 < n := by have := b.isLt; omega
    have h1 : lev j ≤ lev ⟨j + 1, h⟩ := hmono (Fin.le_def.2 (by simp))
    have h2 : lev ⟨j + 1, h⟩ ≤ lev b := hmono (Fin.le_def.2 (by simpa using hb))
    have h3 : lev a ≤ lev j := hmono haj
    have he : lev j = lev ⟨j + 1, h⟩ := by omega
    obtain ⟨d1, d2⟩ := dif_eq_zero lam lev hl j h he
    simp only [d1, d2, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.ModelS.FMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmooth
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.FMem

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun g : Mat n => g a b) :=
  contDiff_apply_apply ℝ ℂ a b

theorem contDiff_det_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → Matrix ι ι ℂ}
    (h : ∀ a b, ContDiff ℝ ∞ fun g => M g a b) : ContDiff ℝ ∞ fun g => (M g).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => h _ _

theorem contDiff_lm (j : Fin n) : ContDiff ℝ ∞ (lm j) :=
  contDiff_det_of_entries fun _ _ => contDiff_entry _ _

theorem contDiff_gm (j : Fin n) : ContDiff ℝ ∞ (gm j) := by
  refine contDiff_det_of_entries fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  refine ContDiff.sum fun k _ => (contDiff_entry _ _).mul ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)

theorem zpow_contDiffOn {f : Mat n → ℂ} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s)
    (h : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℝ ∞ (fun x => f x ^ m) s := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow k
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hf.pow k).inv fun x hx => pow_ne_zero k (h x hx)

open scoped ComplexOrder in

theorem gm_ne_zero (j : Fin n) {g : Mat n} (hg : g ∈ GLs n) : gm j g ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : (g.submatrix (ini j) id)ᴴ *ᵥ v = 0 :=
    (Matrix.self_mul_conjTranspose_mulVec_eq_zero _ v).mp hAv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hAB : g.submatrix (ini j) id * (g⁻¹).submatrix id (ini j) = 1 := by
    have h2 := Matrix.submatrix_mul g g⁻¹ (ini j) id (ini j) Function.bijective_id
    have hi : Function.Injective (ini j) := Fin.castLE_injective _
    rw [Matrix.mul_nonsing_inv g hu, Matrix.submatrix_one _ hi] at h2
    exact h2.symm
  have hBA : ((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  apply hv
  calc v = (((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ) *ᵥ v := by
        rw [hBA, Matrix.one_mulVec]
    _ = ((g⁻¹).submatrix id (ini j))ᴴ *ᵥ ((g.submatrix (ini j) id)ᴴ *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

theorem muZ_antitone {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hlam : Antitone lam) (hlev : Monotone lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : lev a ≤ lev b := hlev hab
  have c1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have c2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

theorem dif_nonneg_of_antitone {v : Fin n → ℤ} (h : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    0 ≤ dif v j := by
  have h1 : v ⟨j + 1, hj⟩ ≤ v j := h (Fin.le_def.mpr (Nat.le_succ _))
  unfold dif
  rw [dif_pos hj]
  omega

theorem lm_ne_zero (j : Fin n) (hj : ¬ (j : ℕ) + 1 < n) {g : Mat n} (hg : g ∈ GLs n) : lm j g ≠ 0 := by
  have hb : Function.Bijective (ini j) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Fin.castLE_injective _, by
      have := j.isLt
      simp only [Fintype.card_fin]
      omega⟩
  have e : lm j g = g.det := Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g
  rw [e]
  exact hg

end GlobalTheory.CompanionTheory.ModelS.FMem

namespace GlobalTheory.CompanionTheory.ModelS

open FMem in

theorem fRaw_mem_SmF : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  intro n lam hlam lev hlev
  refine ⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩
  have key : ContDiffOn ℝ ∞
      (fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j) (GLs n) := by
    refine contDiffOn_prod fun j _ => ContDiffOn.mul ?_
      (zpow_contDiffOn (contDiff_gm j).contDiffOn (fun g hg => gm_ne_zero j hg) _)
    by_cases hj : (j : ℕ) + 1 < n
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (dif_nonneg_of_antitone (muZ_antitone hlam hlev.1) j hj)
      simp only [hk, zpow_natCast]
      exact ((contDiff_lm j).pow k).contDiffOn
    · exact zpow_contDiffOn (contDiff_lm j).contDiffOn (fun g hg => lm_ne_zero j hj hg) _
  exact key.congr fun g hg => Set.indicator_of_mem hg _

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingSegmentProductStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible),
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m)).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m)).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m) |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m) |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing | exact GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing | (intros; apply GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModuleStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_cuspidal_smooth_module : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ IsStable V := by
  first | exact @GlobalTheory.CompanionTheory.StableMod.exists_stable | exact GlobalTheory.CompanionTheory.StableMod.exists_stable | (intros; apply GlobalTheory.CompanionTheory.StableMod.exists_stable <;> assumption)
end

