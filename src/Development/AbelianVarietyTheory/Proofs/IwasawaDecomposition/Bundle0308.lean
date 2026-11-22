import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

open Finset GlobalTheory.SignedHC GlobalTheory.ContragredientPar

theorem goodPar_image {ι : Type} [Fintype ι] {n p q : ℕ} (f : ι → ℚ × Bool) (hf : Function.Injective fun a => (f a).1)
    (hn : Fintype.card ι = n) (hc : ∀ a, ∃ z : ℤ, (f a).1 = ((n : ℚ) - 1) / 2 + z)
    (hq : (univ.filter fun a => (f a).2 = false).card = q) (hpq : p + q = n) : GoodPar n p q (univ.image f) := by
  have hinj : Function.Injective f := fun a c h => hf (congrArg Prod.fst h)
  have hcard : (univ.image f).card = n := by rw [card_image_of_injective _ hinj, card_univ, hn]
  have hminus : SignedHC.nMinus (univ.image f) = q := by
    rw [SignedHC.nMinus, filter_image, card_image_of_injective _ hinj, hq]
  have hsum := nPlus_add_nMinus (univ.image f)
  refine goodPar_iff.2 ⟨⟨?_, hcard, ?_⟩, ?_⟩
  · intro x hx y hy e
    obtain ⟨a, -, rfl⟩ := mem_image.1 hx
    obtain ⟨c, -, rfl⟩ := mem_image.1 hy
    rw [hf e]
  · intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    obtain ⟨a, -, e⟩ := mem_image.1 hs
    have e1 : (f a).1 = x := congrArg Prod.fst e
    rw [← e1]
    exact hc a
  · simp only [signature, Prod.mk.injEq]
    omega

variable {R : Ranks} (P : HCParam R)

theorem b_le_e {a c : Fin R.m} (h : a ≤ c) : P.b a + ((R.t : ℚ) + 3) / 2 ≤ P.e c := by
  have h1 := P.gap_be c
  have h2 := (b_strictMono P).monotone h
  linarith

theorem e_le_b {a c : Fin R.m} (h : c < a) : P.e c + ((R.t : ℚ) + 3) / 2 ≤ P.b a := by
  have hc : c.1 + 1 < R.m := lt_of_le_of_lt (Nat.succ_le_of_lt h) a.2
  have h1 := P.gap_eb c hc
  have h2 : P.b ⟨c.1 + 1, hc⟩ ≤ P.b a := (b_strictMono P).monotone (show c.1 + 1 ≤ a.1 from h)
  linarith

def entAt (j : ℕ) (hj : j ≤ R.m) (s : ℚ) : Fin (R.k - 1) ⊕ Fin R.m ⊕ Fin j × Fin R.t → ℚ × Bool
  | .inl i => (P.v i + s, true)
  | .inr (.inl i) => (-P.b i + s, decide (i.1 ≤ j ∨ Even (i.1 - j)))
  | .inr (.inr x) => (-P.e (Fin.castLE hj x.1) + ((R.t : ℚ) - 1) / 2 - (x.2 : ℕ) + s, true)

theorem entAt_inj (j : ℕ) (hj : j ≤ R.m) (s : ℚ) : Function.Injective fun a => (entAt P j hj s a).1 := by
  have hb : ∀ a : Fin R.t, (0 : ℚ) ≤ (a : ℕ) ∧ ((a : ℕ) : ℚ) + 1 ≤ R.t := fun a =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast a.2⟩
  have hvb : ∀ i (c : Fin R.m) (a : Fin R.t), P.v i ≠ -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) := fun i c a h => by
    have := neg_v_lt_b P i c
    have := b_le_e P (le_refl c)
    have := hb a
    linarith [this.1]
  have hbb : ∀ (i c : Fin R.m) (a : Fin R.t), -P.b i ≠ -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) := fun i c a h => by
    have := hb a
    rcases le_or_gt i c with h' | h'
    · linarith [b_le_e P h', this.1]
    · linarith [e_le_b P h', this.2]
  have hee : ∀ (c c' : Fin R.m) (a a' : Fin R.t), c < c' →
      -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) ≠ -P.e c' + ((R.t : ℚ) - 1) / 2 - (a' : ℕ) := fun c c' a a' h' h => by
    linarith [e_le_b P h', b_le_e P (le_refl c'), (hb a).2, (hb a').1]
  rintro (a | a | ⟨a, x⟩) (c | c | ⟨c, y⟩) h <;> simp only [entAt, add_left_inj] at h
  · rw [(v_strictAnti P).injective h]
  · exact absurd (by linarith) (neg_v_lt_b P a c).ne
  · exact absurd h (hvb _ _ _)
  · exact absurd (by linarith) (neg_v_lt_b P c a).ne
  · rw [(b_strictMono P).injective (neg_injective h)]
  · exact absurd h (hbb _ _ _)
  · exact absurd h.symm (hvb _ _ _)
  · exact absurd h.symm (hbb _ _ _)
  · rcases lt_trichotomy a c with h' | rfl | h'
    · exact absurd h (hee _ _ _ _ h')
    · have : ((x : ℕ) : ℚ) = (y : ℕ) := by linarith
      rw [Fin.ext (Nat.cast_injective this : (x : ℕ) = y)]
    · exact absurd h.symm (hee _ _ _ _ h')

theorem card_minus (j m : ℕ) : ((range m).filter fun i => ¬ (i ≤ j ∨ Even (i - j))).card = (m - j) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [ih]
      rw [Nat.even_iff] at h
      omega
    · rw [card_insert_of_notMem (by simp), ih]
      rw [Nat.even_iff] at h
      omega

theorem card_entAt_false (j : ℕ) (hj : j ≤ R.m) (s : ℚ) :
    (univ.filter fun a => (entAt P j hj s a).2 = false).card = (R.m - j) / 2 := by
  rw [← card_minus j R.m]
  symm
  refine card_bij (fun i hi => .inr (.inl ⟨i, mem_range.1 (mem_filter.1 hi).1⟩)) ?_ ?_ ?_
  · intro i hi
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simpa [entAt] using (mem_filter.1 hi).2
  · intro a _ c _ h
    simpa using h
  · rintro (a | a | a) hx
    · simp [entAt] at hx
    · exact ⟨a.1, mem_filter.2 ⟨mem_range.2 a.2, by simpa [entAt] using hx⟩, rfl⟩
    · simp [entAt] at hx

theorem goodPar_entAt (j : ℕ) (hj : j ≤ R.m) :
    GoodPar (R.rankY j) (sigYD R j).1 (sigYD R j).2 (univ.image (entAt P j hj (if Odd j then -(1 / 2) else 0))) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  obtain ⟨k', hk'⟩ := R.k_even
  obtain ⟨m', hm'⟩ := R.m_even
  obtain ⟨t', ht'⟩ := R.t_odd
  refine goodPar_image _ (entAt_inj P j hj _) ?_ ?_ (card_entAt_false P j hj _) ?_
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Ranks.rankY, Ranks.r]
    omega
  · have hs : ∃ w : ℤ, (if Odd j then -(1 / 2) else 0 : ℚ) = ((R.rankY j : ℚ) - 1) / 2 + w := by
      have hr : R.r = 2 * (k' + m' - 1) + 1 := by unfold Ranks.r; omega
      unfold Ranks.rankY
      rw [hr, ht']
      generalize k' + m' - 1 = n
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · rw [if_neg (by simp)]
        exact ⟨-(n + i * (2 * t' + 1)), by push_cast; ring⟩
      · rw [if_pos (by simp)]
        exact ⟨-(n + i * (2 * t' + 1) + t' + 1), by push_cast; ring⟩
    obtain ⟨w, hw⟩ := hs
    rw [hw]
    rintro (a | a | ⟨a, x⟩)
    · obtain ⟨z, hz⟩ := P.v_int a
      exact ⟨z + w, by simp only [entAt, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := P.b_int a
      exact ⟨-z + w, by simp only [entAt, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := P.e_int (Fin.castLE hj a)
      refine ⟨-z + t' - (x : ℕ) + w, ?_⟩
      have ht : (R.t : ℚ) = 2 * t' + 1 := by exact_mod_cast ht'
      simp only [entAt, hz, ht]; push_cast; ring
  · simp only [sigYD, Ranks.rankY, Ranks.r]
    omega

theorem Dpar_eq (D : D7) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    (Ptw D).Dpar j τ = univ.image (entAt (D.hc τ) j hj (if Odd j then -(1 / 2) else 0)) := by
  ext x
  simp only [TPar.Dpar, TPar.block, mem_image, mem_union, mem_biUnion, mem_filter, mem_univ, true_and, mem_range,
    Sum.exists, Prod.exists, entAt]
  constructor
  · rintro ⟨_, _, (⟨i, e⟩ | ⟨i, e⟩) | ⟨i, hi, _, ⟨a, ha, rfl⟩, e⟩, rfl⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨i.1, hi⟩, ⟨a, ha⟩, rfl⟩)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, a, rfl⟩)
    · exact ⟨_, _, Or.inl (Or.inl ⟨i, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inl (Or.inr ⟨i, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inr ⟨Fin.castLE hj i, i.2, _, ⟨a.1, a.2, rfl⟩, rfl⟩, rfl⟩

theorem goodPar_parB (D : D7) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y j).rank ((D.sp.Y j).sig (tauE D τ)).1 ((D.sp.Y j).sig (tauE D τ)).2 (parB (Ptw D) j τ) := by
  rw [D.sp.Y_rank j hj, D.Y_sigval j hj, parB, Dpar_eq D j hj]
  exact GlobalTheory.RealGeo.FrameModels.goodPar_dualPar (goodPar_entAt (D.hc τ) j hj)

theorem goodPar_parB_last (D : D7) (τ : D.what₂.Tau) :
    GoodPar D.sp.X'.rank (D.sp.X'.sig (tauE D τ)).1 (D.sp.X'.sig (tauE D τ)).2 (parB (Ptw D) D.R.m τ) := by
  have h := goodPar_parB D D.R.m le_rfl τ
  rw [D.sp.Y_rank _ le_rfl] at h
  rw [GlobalTheory.ChiGrid.sig_X'_eq_sig_Y, D.sp.X'_rank]
  exact h

theorem nonempty_modelY (h : GlobalTheory.Published.DiscreteSeriesExists) (D : D7) (j : ℕ) :
    Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))) :=
  GlobalTheory.Published.dsExists_of_discreteSeriesExists h D _ _ (D.sp.Y_sig _) (goodPar_parB D _ (min_le_right _ _))

theorem nonempty_modelX (h : GlobalTheory.Published.DiscreteSeriesExists) (D : D7) :
    Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m)) :=
  GlobalTheory.Published.dsExists_of_discreteSeriesExists h D _ _ D.sp.X'_sig (goodPar_parB_last D)

theorem labE_embLL (D : D7) (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem labE_lab_embLL (D : D7) (ρ : D.what₂.Tau) : labE D.what₂.embLL (lab D.what₂.embLL ρ) = tauE D ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_embLL D ρ)⟩
  unfold lab
  rw [dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rcases hs with hs | hs
  · exact hs
  · exfalso
    rw [labE_embLL] at hs
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem exists_models : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7,
    ((∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m)))) ∧ Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))) ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        (∀ i τ a, (MW i D.what₂.embLL).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
          GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D
  refine ⟨⟨nonempty_modelY h D, nonempty_modelX h D⟩, fun Ks _ _ hK => ?_⟩
  obtain ⟨MW, hMW⟩ := GlobalTheory.RealGeo.FrameModels.exists_frameKs h D Ks hK
  exact ⟨MW, fun i => hMW.2 i _ (labE_lab_embLL D), hMW⟩

theorem order_embLL (D : D7) (i : Fin D.R.m) (M : DSModel (Wc D i) (parAt (Wc D i) D.what₂.embLL)) (τ : D.what₂.Tau)
    (a : Fin (Wc D i).rank) : M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1) := by
  have he := M.enum τ
  have e : parAt (Wc D i) D.what₂.embLL τ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) D.what₂.embLL τ) :=
    if_pos (labE_lab_embLL D τ)
  rw [e] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (Formalism.IndefR.FWT.rank_Wc i) (GlobalTheory.RealGeo.FrameModels.sig_add i τ) he a).2

end GlobalTheory.ChainModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

section GenP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped TensorProduct

theorem val_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  have h1 : v.valuation F (algebraMap (𝓞 F) F (g : 𝓞 F)) < 1 := (v.valuation_lt_one_iff_mem _).2 h
  have h2 : ((g : v.adicCompletion F)) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by
    simp only [map_natCast]
  rw [h2]
  exact lt_of_eq_of_lt (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (g : 𝓞 F))) h1

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : v.adicCompletion F) (hg : Valued.v g < 1)
    (X W : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hW : ∀ a b, W a b ∈ v.adicCompletionIntegers F)
    (hX : ∀ a b, X a b = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b + g * W a b) :
    redM F v X = 1 := by
  have hgi : g ∈ v.adicCompletionIntegers F := le_of_lt hg
  have h1 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F := by
    intro a b
    by_cases e : a = b
    · subst e
      rw [Matrix.one_apply_eq]
      exact one_mem _
    · rw [Matrix.one_apply_ne e]
      exact zero_mem _
  ext a b
  have hm : X a b ∈ v.adicCompletionIntegers F := by
    rw [hX]
    exact add_mem (h1 a b) (mul_mem hgi (hW a b))
  have hz : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨g, hgi⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Valuation.integer.integers (Valued.v (R := v.adicCompletion F))).isUnit_iff_valuation_eq_one.1 hu
    exact absurd this (ne_of_lt hg)
  have e : (⟨X a b, hm⟩ : v.adicCompletionIntegers F) =
      ⟨(1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b, h1 a b⟩ + ⟨g, hgi⟩ * ⟨W a b, hW a b⟩ := by
    exact Subtype.ext ((hX a b).trans rfl)
  simp only [redM]
  rw [dif_pos hm, e, map_add, map_mul, hz, zero_mul, add_zero]
  by_cases ab : a = b
  · subst ab
    simp only [Matrix.one_apply_eq]
    exact map_one _
  · simp only [Matrix.one_apply_ne ab]
    exact map_zero _

theorem mem_Uloc_of_princ {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ} (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH S G H lam)
    (hLb : ∀ b : Fin n, (Pi.single b 1 : Fin n → E) ∈ S.Lb)
    (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (hfr : V.fr i v h = 1)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL σ J v S.Lb)
    (hc : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) :
    x ∈ S.Uloc v := by
  have hint : ∀ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      G.phi i v h (z a) ∈ v.adicCompletionIntegers F := by
    intro z hz a
    have := (V.fr_lat i v h (fun b => G.phi i v h (z b))).1 ⟨z, hz, fun _ => rfl⟩ a
    rw [hfr] at this
    simpa using this
  have hcol : ∀ b : Fin n, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + (gp i : E ⊗[F] v.adicCompletion F) * z a := by
    intro b
    have e1 : (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single b 1 : Fin n → E) j)) =
        (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) := by
      funext j
      by_cases e : j = b
      · subst e
        simp
      · simp [e]
    have hb : (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
      rw [← e1]
      exact Submodule.subset_span ⟨_, hLb b, rfl⟩
    obtain ⟨z, hz, e⟩ := hc _ hb
    refine ⟨z, hz, fun a => ?_⟩
    have := congrFun e a
    rw [Matrix.mulVec_single_one] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
    rw [← this]
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  choose Z hZ hZe using hcol
  refine (V.mem i v h x hx).2 ⟨1, one_mem _, ?_⟩
  have key : redM F v (G.mat i v h (V.fr i v h) x) = 1 := by
    rw [hfr]
    refine redM_eq_one v (gp i : v.adicCompletion F) (val_nat_lt_one v (gp i) h) _
      (fun a b => G.phi i v h (Z b a)) (fun a b => hint _ (hZ b) a) fun a b => ?_
    have e2 : G.mat i v h 1 x a b = G.phi i v h ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) := by
      simp [GLoc.mat, bc]
    rw [e2, hZe b a, map_add, map_mul, map_natCast]
    congr 1
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  rw [key]
  rfl

end GenP

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_rfl_apply {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_rfl_hom {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_rfl_apply R g

theorem reL_rfl {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem co_rfl (S : HSpace E) : co S rfl = Formalism.L2.Herm.crd S :=
  LinearEquiv.ext fun x => funext fun j => by simp [co, Formalism.L2.Herm.crd]

theorem tie_of_forms (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (hO : Crd.Ortho S)
    {σ : E →ₐ[F] E} (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    {f : ℕ} {gp : Fin 2 → ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (hbad : bad = {v | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal})
    (St : StepLevel F E σ J 1 f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH St G H lam) (hfr : ∀ a v h, V.fr a v h = 1)
    (hLb : ∀ x, x ∈ St.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range)
    {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    (y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls St)))
    (lat : cls → Submodule (𝓞 E) (Fin n → E))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
      ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) St.Lb)
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ St.U.map (MulAut.conj (y c).1).toMonoidHom) :
    ∃ (lattice₂ : cls → Submodule (𝓞 E) S.V) (levP : Formalism.L2.Herm.StepLevel0 hc S gp (Formalism.L2.Herm.crdLat S S.L0))
      (clsP : Formalism.L2.Herm.ClassTie hc S (Formalism.L2.Herm.crdLat S S.L0) levP.U stab lattice₂),
      SameCar h (Formalism.L2.Herm.crdLat S S.L0) St.Lb levP.Uloc St.Uloc levP.U St.U
        (fun c => (clsP.y c).1) (fun c => (y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => (stabI c s).1) ∧
      ∀ c, lat c = (lattice₂ c).map (((co S h : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := hJ.trans (by ext a b; simp)
  subst hbad
  have hL : St.Lb = Formalism.L2.Herm.crdLat S S.L0 := by
    ext x
    rw [hLb x, ← hO.mem_standardLattice_iff_integral_coords rfl x]
    unfold Formalism.L2.Herm.crdLat
    rw [show Crd.co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := fun v hv =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hv))
  have hs : ∀ b : Fin S.rank, (Pi.single b 1 : Fin S.rank → E) ∈ St.Lb := by
    intro b
    refine (hLb _).2 fun j => ?_
    by_cases e : j = b
    · subst e
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [e]⟩
  refine ⟨fun c => (lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E)),
    { Uloc := St.Uloc
      Uloc_lev := fun v => hL ▸ St.Uloc_lev v
      Uloc_hyp := fun v h0 h1 => ?_
      Uloc_g := fun i v hv x hx => ?_
      U := St.U
      U_eq := St.U_eq },
    { y := y
      y_bij := y_bij
      y_lat := fun c x => ?_
      stabI := stabI
      stabI_inj := stabI_inj
      stabI_range := stabI_range }, ⟨?_, fun v => ?_, ?_, fun c => ?_, fun c s => ?_⟩, fun c => ?_⟩
  · rw [St.Uloc_hyp v (by rintro (h | h); exacts [h0 h, h1 h]) (hone v), hL]
  · rw [← hL] at hx
    exact mem_Uloc_of_princ St G V hs i v hv (hfr i v hv) x hx.1 hx.2
  · have e : Formalism.L2.Herm.crdLat S ((lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E))) = lat c :=
      Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)
    rw [e, ← hL]
    exact y_lat c x
  · rw [reL_rfl, hL]
  · show St.Uloc v = (St.Uloc v).map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · show St.U = St.U.map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · exact (reGL_rfl_apply _ _).symm
  · exact (reGL_rfl_apply _ _).symm
  · rw [show co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
    exact (Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)).symm

end Tr

set_option maxHeartbeats 4000000 in

theorem clsP_hermitian : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  intro B X I hI hP l Z H F hstd hcar u
  obtain ⟨hs, -, hX', -⟩ := hI.spaces
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  have hr := (hstd u).1.what₂
  have hLb : ∀ x, x ∈ (F u).clsP.lev.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    refine (hr.lb x).trans ⟨fun hx j => ?_, fun hx j => ?_⟩
    · obtain ⟨r, e, -⟩ := hx j
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e⟩ := hx j
      exact ⟨r, e.symm, fun _ => one_dvd r⟩
  exact tie_of_forms (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) oX' rfl rfl rfl (F u).clsP.lev (F u).gl
    (F u).glevP (hstd u).1.frP hLb (F u).clsP.y (F u).clsP.y_bij (F u).clsP.lat (F u).clsP.y_lat (F u).clsP.stabI
    (F u).clsP.stabI_inj (F u).clsP.stabI_range

end GlobalTheory.Mem.Col2.HAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  first | exact @GlobalTheory.Mem.TopGram.topGram | exact GlobalTheory.Mem.TopGram.topGram | (intros; apply GlobalTheory.Mem.TopGram.topGram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitaryStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  first | exact @GlobalTheory.DefU.iSup_range_weight_eq_top | exact GlobalTheory.DefU.iSup_range_weight_eq_top | (intros; apply GlobalTheory.DefU.iSup_range_weight_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Df.mtHL_good_basis | exact GlobalTheory.Mem.Df.mtHL_good_basis | (intros; apply GlobalTheory.Mem.Df.mtHL_good_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStepStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_classMap_above_lastStep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i → Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) := by
  first | exact @GlobalTheory.Mem.Col2.TC.nonempty_clDown | exact GlobalTheory.Mem.Col2.TC.nonempty_clDown | (intros; apply GlobalTheory.Mem.Col2.TC.nonempty_clDown <;> assumption)
end

