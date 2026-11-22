import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdFamL
section
open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult

variable {n : ℕ}

def AdFamL (lev : Fin n → ℕ) {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n))
    (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ c d, lev c = lev d → ∀ i, (X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d) =
      ∑ j, M c d j i • evB lev X1 X2 (w j)

theorem ad_letter {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {X1 X2 : Fin n → Fin n → Module.End ℂ W}
    (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (s : Bool) (a b : Fin n) :
    (X1 c d + X2 c d) * evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) -
        evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) * (X1 c d + X2 c d) =
      (if d = a then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, c, b)) else 0) -
        (if b = c then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, d)) else 0) := by
  obtain ⟨h1, h2, h3⟩ := hX
  simp only [evB, FreeAlgebra.lift_ι_apply]
  by_cases hab : lev a = lev b
  · have e1 : d = a → lev c = lev b := fun h => by rw [hcd, h, hab]
    have e2 : b = c → lev a = lev d := fun h => by rw [hab, h, hcd]
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) =
        if d = a then (if s = true then X1 c b else X2 c b) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e1 h) h'
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) =
        if b = c then (if s = true then X1 a d else X2 a d) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e2 h) h'
    rw [k1, k2, if_pos hab]
    cases s
    · have e := h2 c d a b hcd hab
      have k := (h3 c d a b hcd hab).eq
      simp only [Bool.false_eq_true, if_false, add_mul, mul_add]
      rw [k, ← e]
      abel
    · have e := h1 c d a b hcd hab
      have k := (h3 a b c d hab hcd).eq
      simp only [if_true, add_mul, mul_add]
      rw [k, ← e]
      abel
  · have e1 : d = a → ¬ lev c = lev b := fun h => by rw [hcd, h]; exact hab
    have e2 : b = c → ¬ lev a = lev d := fun h => by rw [← hcd, ← h]; exact hab
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e1 h)
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e2 h)
    rw [k1, k2, if_neg hab]
    simp

theorem exists_adFamL (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFamL lev w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro W _ _ X1 X2 _ c d _ i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Bool × Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) -
        (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨s, i1, i2⟩ ⟨t, j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩
    · rintro W _ _ X1 X2 hX c d hcd ⟨s, a, b⟩
      have h := ad_letter hX hcd s a b
      simp only [Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro W _ _ X1 X2 hX c d hcd ⟨i, i'⟩
      have e1 := h2 W X1 X2 hX c d hcd i
      have e2 := h2' W X1 X2 hX c d hcd i'
      have : (X1 c d + X2 c d) * evB lev X1 X2 (w i * w' i') - evB lev X1 X2 (w i * w' i') * (X1 c d + X2 c d) =
          ((X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d)) * evB lev X1 X2 (w' i') +
            evB lev X1 X2 (w i) *
              ((X1 c d + X2 c d) * evB lev X1 X2 (w' i') - evB lev X1 X2 (w' i') * (X1 c d + X2 c d)) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro W _ _ X1 X2 hX c d hcd (i | i)
      · simp [Fintype.sum_sum_type, h2 W X1 X2 hX c d hcd]
      · simp [Fintype.sum_sum_type, h2' W X1 X2 hX c d hcd]
    · simp [Fintype.sum_sum_type]

theorem AdFamL.comm {lev : Fin n → ℕ} {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFamL lev w M) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (t : ι → ℂ) :
    (X1 c d + X2 c d) * evB lev X1 X2 (∑ i, t i • w i) - evB lev X1 X2 (∑ i, t i • w i) * (X1 c d + X2 c d) =
      evB lev X1 X2 (∑ j, (M c d *ᵥ t) j • w j) := by
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 W X1 X2 hX c d hcd, Finset.smul_sum, Matrix.mulVec, dotProduct,
    Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invL : InvL := by
  classical
  intro n lev V _ _ X1 X2 L a hX hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFamL lev a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, lev c = lev d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, lev c = lev d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, lev c = lev d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ Y1 Y2 hY c d hcd
    have := hM.comm hY hcd t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : evB lev Y1 Y2 (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.PairMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

def IsHK (H : Subgroup G) (E : Set G) : Prop :=
  (∀ h ∈ H, ∀ g, h * g ∈ E ↔ g ∈ E) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, g * x ∈ E ↔ g ∈ E

theorem IsHK.compl {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsHK H Eᶜ := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  exact ⟨fun h hh g => not_congr (h1 h hh g), K, hK, fun g x hx => not_congr (h2 g x hx)⟩

theorem IsHK.inter {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∩ E') := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨h1', K', hK', h2'⟩ := hE'
  refine ⟨fun h hh g => and_congr (h1 h hh g) (h1' h hh g), K ⊓ K', ?_, fun g x hx =>
    and_congr (h2 g x hx.1) (h2' g x hx.2)⟩
  exact hK.inter hK'

theorem IsHK.union {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∪ E') := by
  have := (hE.compl.inter hE'.compl).compl
  rwa [Set.compl_inter, compl_compl, compl_compl] at this

theorem IsHK.isOpen {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsOpen E := by
  obtain ⟨-, K, hK, h2⟩ := hE
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hn : (fun y => g⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
  filter_upwards [hn] with y hy
  have e : y = g * (g⁻¹ * y) := by group
  rw [e]
  exact (h2 g _ hy).2 hg

theorem isHK_doubleCoset (H K : Subgroup G) (hK : IsOpen (K : Set G)) (c : G) :
    IsHK H {g | ∃ a ∈ H, ∃ x ∈ K, g = a * c * x} := by
  refine ⟨fun h hh g => ⟨?_, ?_⟩, K, hK, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨h⁻¹ * a, mul_mem (inv_mem hh) ha, x, hx, by
      have e2 : g = h⁻¹ * (h * g) := by group
      rw [e2, e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨h * a, mul_mem hh ha, x, hx, by group⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨a, ha, x * y⁻¹, mul_mem hx (inv_mem hy), by
      rw [← mul_assoc, ← e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x * y, mul_mem hx hy, by group⟩

def stabSub {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem cInd_right_inv (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, f.1.1.1 (g * x) = f.1.1.1 g := by
  refine ⟨stabSub (ind H σ) f.1.1, f.1.2, fun g x hx => ?_⟩
  have h : ind H σ x f.1.1 = f.1.1 := hx
  exact congrArg (fun v : indSpace H σ => v.1 g) h

theorem exists_indicator (H : Subgroup G) (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E)
    (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, (∀ g ∈ E, f'.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → f'.1.1.1 g = 0) := by
  classical
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H σ f
  let b : G → W := fun g => if g ∈ E then f.1.1.1 g else 0
  have hind : b ∈ indSpace H σ := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    by_cases hg : g ∈ E
    · have hg' : (h : G) * g ∈ E := (h1 h h.2 g).2 hg
      simp only [b, if_pos hg, if_pos hg', e]
    · have hg' : (h : G) * g ∉ E := fun c => hg ((h1 h h.2 g).1 c)
      simp only [b, if_neg hg, if_neg hg', map_zero]
  have hsm : (⟨b, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ) (K ⊓ L) (hK.inter hL) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show b (g * x) = b g
    by_cases hg : g ∈ E
    · have hg' : g * x ∈ E := (h2 g x hx.1).2 hg
      simp only [b, if_pos hg, if_pos hg', hLi g x hx.2]
    · have hg' : g * x ∉ E := fun c => hg ((h2 g x hx.1).1 c)
      simp only [b, if_neg hg, if_neg hg']
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H σ)) ∈ cIndSpace H σ := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g ?_⟩
    intro h0
    apply hg
    show b g = 0
    by_cases hgE : g ∈ E
    · simp only [b, if_pos hgE]; exact h0
    · simp only [b, if_neg hgE]
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun g hg => if_pos hg, fun g hg => if_neg hg⟩

theorem exists_cInd_value (H : Subgroup G) (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (c : G) (w : W) : ∃ e : cIndSpace H σ, e.1.1.1 c = w := by
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hσ w)
  have h1O : (1 : G) ∈ O := by
    have : (1 : H) ∈ (Subtype.val ⁻¹' O : Set H) := by rw [hOe]; simp
    exact this
  have hn : (fun x => c * x * c⁻¹) ⁻¹' O ∈ 𝓝 (1 : G) :=
    (hO.preimage (by fun_prop)).mem_nhds (by simpa using h1O)
  obtain ⟨K, hKo, hKc, hKO⟩ := hbase _ hn
  obtain ⟨B, hB, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc c w (by
    intro a x hx e
    have hax : (a : G) ∈ O := by rw [e]; exact hKO hx
    have : a ∈ (Subtype.val ⁻¹' O : Set H) := hax
    rw [hOe] at this
    exact this)
  refine ⟨B, ?_⟩
  have h := hB 1 1 (one_mem K)
  simpa using h

end Abstract

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev embedding₂ (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : ((eGP m j ⟨false, a⟩ : Fin (m + j + 1)) : ℕ) = a := by
  simp [eGP, stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : ((eGP m j ⟨true, b⟩ : Fin (m + j + 1)) : ℕ) = m + b := by
  simp [eGP, stdSum]

theorem mem_mirabolicParabolic_iff (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
      ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
        (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
  show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
  rw [mem_parab_iff]
  constructor
  · intro h b a
    exact h true false b a (by decide)
  · intro h x y i l hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem isOpen_ker_dpow (n : ℕ) (s : ℝ) :
    IsOpen (((dpow (k := k) n s).ker : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
  IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow (s : ℂ))

end Conc

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

section Group

variable (k : Type) [Field k]

abbrev Qp (i t : ℕ) : Subgroup (GL (Fin (i + t)) k) := parab k (two (stdSum (rfl : i + t = i + t)))

def qBlocks (i t : ℕ) : Qp k i t →* GL (Fin i) k × GL (Fin t) k :=
  MonoidHom.prod
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) false).comp (leviProj k (two (stdSum rfl))))
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) true).comp (leviProj k (two (stdSum rfl))))

def uM (n : ℕ) (y : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd y), MirU_le_Mir k n ⟨_, rfl⟩⟩

def topV (i t : ℕ) (x : Fin i → k) : Fin (i + t) → k := Fin.append x 0

def midV (i t : ℕ) (v : Fin t → k) : Fin (i + t) → k := Fin.append 0 v

theorem uM_add (n : ℕ) (a b : Fin n → k) : uM k n (a + b) = uM k n a * uM k n b := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (a + b)) = unip k n (Multiplicative.ofAdd a) * unip k n (Multiplicative.ofAdd b)
  rw [ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM k n 0 = 1 := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd 0) = 1
  rw [ofAdd_zero, map_one]

theorem uM_mem (n : ℕ) (y : Fin n → k) : uM k n y ∈ MirUin k n := ⟨_, rfl⟩

theorem exists_uM_of_mem (n : ℕ) {u : Mir k n} (hu : u ∈ MirUin k n) : ∃ y, u = uM k n y := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨v.toAdd, Subtype.ext hv.symm⟩

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (y : Fin n → k) :
    levi k n g * uM k n y = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec y) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd y)

theorem topV_add_midV (i t : ℕ) (x : Fin i → k) (v : Fin t → k) :
    topV k i t x + midV k i t v = Fin.append x v := by
  funext j
  induction j using Fin.addCases <;> simp [topV, midV]

theorem exists_top_mid (i t : ℕ) (y : Fin (i + t) → k) : ∃ x v, y = topV k i t x + midV k i t v := by
  refine ⟨fun j => y (Fin.castAdd t j), fun j => y (Fin.natAdd i j), ?_⟩
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def qRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (Qp k i t) (Jacquet τ (MirUin k i) ⊗[ℂ] W) :=
  twist ((extTensor (psiMinus k τ) σ).comp (qBlocks k i t))
    ((detChar (Fin t) (absPow k (1 : ℂ))).comp ((MonoidHom.snd _ _).comp (qBlocks k i t)))

abbrev hRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (HPG k i t) (V ⊗[ℂ] W) :=
  (extTensor τ σ).comp (pgProj k i t)

def clT (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    V ⊗[ℂ] W →ₗ[ℂ] Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  LinearMap.rTensor W (twKer τ (MirUin k i) 1).mkQ

def evL {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W} (p : Mir k (i + t)) :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] V ⊗[ℂ] W :=
  (LinearMap.proj p) ∘ₗ (indSpace (HPG k i t) (hRep τ σ)).subtype ∘ₗ (smoothPart (ind (HPG k i t) (hRep τ σ))).subtype ∘ₗ
    (cIndSpace (HPG k i t) (hRep τ σ)).subtype

def fibV {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (v : Fin t → k) : V ⊗[ℂ] W :=
  f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g)

def fibInt {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) : Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  clT τ W (smInt μ (fibV f g))

end Rep

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_has_generic_irreducible_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ → IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧ IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  first | exact @GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | exact GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closed : GEClosed := by
  first | exact @GlobalTheory.CompanionTheory.GE.geClosed | exact GlobalTheory.CompanionTheory.GE.geClosed | (intros; apply GlobalTheory.CompanionTheory.GE.geClosed <;> assumption)
end

