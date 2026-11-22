import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0871
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0869
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DoubleCosetSeparation
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.DcosSep
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.CompanionTheory.IwahoriContraction in

private theorem conj_diag {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (n : ℕ) (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w)
    (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m t : GLw n w, ((∀ i j : Fin n, i ≠ j → t.val i j = 0) ∧ ∀ i, Valued.v (t.val i i) = 1) ∧
      m⁻¹ * δ * m = tdiag ϖ y * t := by
  have hd : ∃ a ∈ iwGL n w, ∃ b ∈ iwGL n w, δ = a * tdiag ϖ y * b := by
    by_contra h
    exact hδ (if_neg h)
  obtain ⟨a, ha, b, hb, hab⟩ := hd
  obtain ⟨⟨U, hU⟩, -, hcpt, -⟩ := GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois.1 (w.adicCompletion E) n
  have hcomp : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  have h0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hid : ∀ g : GL (Fin n) (w.adicCompletion E),
      Matrix.GeneralLinearGroup.map ((RingEquiv.refl (w.adicCompletion E) : _ ≃+* _) : _ →+* _) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  have hlt : ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 (v_lt_one_of_ordL_eq_one w h0 hϖ)
  have hmax : ∀ x : w.adicCompletion E, ValuativeRel.valuation (w.adicCompletion E) x < 1 →
      ValuativeRel.valuation (w.adicCompletion E) x ≤
        ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := fun x hx =>
    (hequiv.le_iff_le).2 (v_le_of_ordL_eq_one w h0 hϖ ((GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).1 hx))
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hgap : ∀ i l, i < l → ValuativeRel.valuation (w.adicCompletion E) (e i) ≤
      ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) *
        ValuativeRel.valuation (w.adicCompletion E) (e l) := fun i l h => by
    obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((c + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (c + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (c + 1)
        ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hlt.le (Nat.succ_le_succ (Nat.zero_le c))
      _ = _ := pow_one _
  have hx : ((tdiag ϖ y : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e := by
    rw [tdiag, GlobalTheory.SmGL.val_diagT]
  have hmem : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (tdiag ϖ y : GLw n w) :=
    ⟨a, (mem_iwGL_iff w n a).1 ha, b, (mem_iwGL_iff w n b).1 hb, hab⟩
  obtain ⟨m, -, t, ht, h⟩ := GlobalTheory.CompanionTheory.TwContraction.contraction U hU hcpt (RingEquiv.refl _)
    (fun _ => rfl) (fun g hg => by rw [hid]; exact hg) _ hlt hmax e (fun i => Units.ne_zero _) hgap _ hx δ hmem
  rw [hid] at h
  exact ⟨m, t, torusO_subset_TO w n t ht, h⟩

private theorem sep_of_dcos {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (n : ℕ) (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w)
    (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) : δ.val.charpoly.Separable := by
  obtain ⟨m, t, ⟨hoff, hdiag⟩, h⟩ := conj_diag w ϖ hϖ n y hy δ hδ
  let d : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * t.val i i
  have ht0 : ∀ i, t.val i i ≠ 0 := fun i h0 => by
    have := hdiag i
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hord : ∀ i, ordL (d i) = y i := fun i => by
    simp only [d]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (ht0 i),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hdiag i, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  have hinj : Function.Injective d := fun i j hij => hy.injective (by rw [← hord i, ← hord j, hij])
  have hmat : (m⁻¹ * δ * m : GLw n w).val = Matrix.diagonal d := by
    rw [h, Units.val_mul, tdiag, GlobalTheory.SmGL.val_diagT]
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst hij
      simp [d]
    · simp [hoff i j hij, hij]
  have hcp : δ.val.charpoly = ∏ i, (X - C (d i)) := by
    have h1 : (m⁻¹ * δ * m : GLw n w).val.charpoly = δ.val.charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj' m δ.val
    rw [← h1, hmat, Matrix.charpoly_diagonal]
  rw [hcp]
  exact separable_prod_X_sub_C_iff.2 hinj

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosSep :=
  _root_.UpperTheory.Reformulated.B.DoubleCosetSeparation.dcosSep
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SupportTranslate
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem swap3 {α β γ : Type} (u : β → γ → ℂ) (v : β → γ → α → ℂ) (Cs : Set β) (hC : Cs.Finite)
    (hCs : ∀ c, c ∉ Cs → ∀ x, u c x = 0) (hA : ∀ c, (Function.support (u c)).Finite)
    (hv : ∀ c x, (Function.support (v c x)).Finite) (r : β → ℂ) (hr : ∀ c x, ∑ᶠ X, v c x X = r c) :
    ∑ᶠ X : α, ∑ᶠ c, ∑ᶠ x, u c x * v c x X = ∑ᶠ c, (∑ᶠ x, u c x) * r c := by
  set Cf : Finset β := hC.toFinset with hCf
  let Af : β → Finset γ := fun c => (hA c).toFinset
  have hin : ∀ X : α, ∑ᶠ c, ∑ᶠ x, u c x * v c x X = ∑ p ∈ Cf.sigma Af, u p.1 p.2 * v p.1 p.2 X := by
    intro X
    rw [← Finset.sum_sigma' Cf Af (fun c x => u c x * v c x X)]
    rw [finsum_eq_sum_of_support_subset (s := Cf)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      refine finsum_eq_sum_of_support_subset _ ?_
      intro x hx
      simp only [Function.mem_support] at hx
      simp only [Af, Set.Finite.coe_toFinset, Function.mem_support]
      exact left_ne_zero_of_mul hx
    · intro c hc
      simp only [Function.mem_support] at hc
      simp only [hCf, Set.Finite.coe_toFinset]
      by_contra hcs
      exact hc (by simp [hCs c hcs])
  simp_rw [hin]
  have hfs : ∑ᶠ X : α, ∑ p ∈ Cf.sigma Af, u p.1 p.2 * v p.1 p.2 X =
      ∑ p ∈ Cf.sigma Af, ∑ᶠ X : α, u p.1 p.2 * v p.1 p.2 X := by
    refine finsum_sum_comm (Cf.sigma Af) (fun (X : α) (p : (_ : β) × γ) => u p.1 p.2 * v p.1 p.2 X) fun p _ => ?_
    refine (hv p.1 p.2).subset fun X hX => ?_
    simp only [Function.mem_support] at hX ⊢
    exact right_ne_zero_of_mul hX
  rw [hfs]
  · have hstep : ∀ p : (_ : β) × γ, ∑ᶠ X, u p.1 p.2 * v p.1 p.2 X = u p.1 p.2 * r p.1 := by
      intro p
      have := smul_finsum (u p.1 p.2) (v p.1 p.2)
      simp only [smul_eq_mul] at this
      rw [← this, hr]
    simp_rw [hstep]
    rw [← Finset.sum_sigma' Cf Af (fun c x => u c x * r c)]
    rw [finsum_eq_sum_of_support_subset (s := Cf)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      exact (finsum_eq_sum_of_support_subset (s := Af c) (u c) (by simp [Af])).symm
    · intro c hc
      simp only [Function.mem_support] at hc
      simp only [hCf, Set.Finite.coe_toFinset]
      by_contra hcs
      refine hc ?_
      have : (fun x => u c x) = fun _ => 0 := funext (hCs c hcs)
      simp [this]

section Tr

variable {N : Type} [CommGroup N] (L : Subgroup N)

private theorem out_val (φ : N → ℂ) (hφ : ∀ x, ∀ l ∈ L, φ (x * l) = φ x) (g : N) :
    φ (QuotientGroup.mk g : N ⧸ L).out = φ g := by
  obtain ⟨⟨y, hy⟩, hy'⟩ := QuotientGroup.mk_out_eq_mul L g
  rw [hy']
  exact hφ g y hy

private theorem sum_translate (φ : N → ℂ) (hφ : ∀ x, ∀ l ∈ L, φ (x * l) = φ x) (t : N) :
    ∑ᶠ x : N ⧸ L, φ (x.out * t) = ∑ᶠ x : N ⧸ L, φ x.out := by
  have e : ∀ x : N ⧸ L, φ (x.out * t) = φ (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L) x).out := by
    intro x
    rw [← out_val L φ hφ (x.out * t)]
    congr 2
    simp
  simp_rw [e]
  exact finsum_comp_equiv (f := fun x : N ⧸ L => φ x.out) (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L))

private theorem support_translate (φ : N → ℂ) (hφ : ∀ x, ∀ l ∈ L, φ (x * l) = φ x) (t : N)
    (hf : (Function.support fun x : N ⧸ L => φ x.out).Finite) :
    (Function.support fun x : N ⧸ L => φ (x.out * t)).Finite := by
  refine (hf.preimage (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L)).injective.injOn).subset fun x hx => ?_
  simp only [Function.mem_support, Set.mem_preimage] at hx ⊢
  rw [← out_val L φ hφ (x.out * t)] at hx
  have : (QuotientGroup.mk (x.out * t) : N ⧸ L) = Equiv.mulRight (QuotientGroup.mk t : N ⧸ L) x := by simp
  rwa [this] at hx

end Tr

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private def dl (w : Pl E) (m : GLw a w × GLw b w) : ℂ := absHalf w (m.1.val.det ^ b / m.2.val.det ^ a)

private theorem dl_mul (w : Pl E) (m m' : GLw a w × GLw b w) : dl w (m * m') = dl w m * dl w m' := by
  unfold dl
  have h1 := Matrix.GeneralLinearGroup.det_ne_zero m.1
  have h2 := Matrix.GeneralLinearGroup.det_ne_zero m.2
  have h3 := Matrix.GeneralLinearGroup.det_ne_zero m'.1
  have h4 := Matrix.GeneralLinearGroup.det_ne_zero m'.2
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (div_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2))
    (div_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h4))]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.det_mul, mul_pow]
  field_simp

private def Sm (h : a + b = n) (w : Pl E) (φ : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
    φ (blk h w m (Multiplicative.toAdd x.out))

private theorem K_of_int (h : a + b = n) (w : Pl E)
    (l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) (hl : l ∈ intMat a b w) :
    blk h w 1 (Multiplicative.toAdd l) ∈ KGL w n := by
  have e := (GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w).1
  rw [← e] at hl
  exact hl

private theorem right_L (h : a + b = n) (w : Pl E) (φ : GLw n w → ℂ) (hφ : ∀ k ∈ KGL w n, ∀ x, φ (x * k) = φ x)
    (m : GLw a w × GLw b w) (x l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))
    (hl : l ∈ intMat a b w) :
    φ (blk h w m (Multiplicative.toAdd (x * l))) = φ (blk h w m (Multiplicative.toAdd x)) := by
  rw [toAdd_mul, GlobalTheory.CompanionTheory.IntDec.blk_add]
  exact hφ _ (K_of_int h w l hl) _

private theorem inv_blk (h : a + b = n) (w : Pl E) (c m : GLw a w × GLw b w)
    (Y X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w c Y)⁻¹ * blk h w m X =
      blk h w (c⁻¹ * m) (X + -(((c⁻¹ * m).1⁻¹).val * Y * (c⁻¹ * m).2.val)) := by
  rw [inv_mul_eq_iff_eq_mul, GlobalTheory.LeviFubini.blk_mul_blk]
  simp

private theorem ct_bi (h : a + b = n) (w : Pl E) (F : GLw n w → ℂ) (hF : IsHecke (KGL w n) F)
    (k : GLw a w × GLw b w) (hk : k ∈ K2 a b w) (m : GLw a w × GLw b w) :
    ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hkN : GlobalTheory.BCT.CtLevel.dgM h w k ∈ KGL w n := by
    rw [← GlobalTheory.CompanionTheory.IntDec.blk_zero_eq_dgM]
    exact (GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w).2 (Subgroup.mem_map_of_mem _ hk)
  exact GlobalTheory.BCT.CtLevel.ct_inv h w (KGL w n) F
    (fun k hk x hx => mul_mem (mul_mem (inv_mem hk) hx) hk) (fun y hy x => hF.2 y hy x) k
    (Subgroup.mem_prod.1 hk).1 (Subgroup.mem_prod.1 hk).2 hkN m

end Conc

theorem ctMul : CtMul := by
  intro E _ _ _ w n a b h f g hf hg
  obtain ⟨-, -, hKo, hKc, -, -, -⟩ := unitHecke E n a b w
  have hfg : IsHecke (KGL w n) (cv (KGL w n) f g) := cvHecke _ (KGL w n) hKo hKc f g hf hg
  have hct : ∀ φ, IsHecke (KGL w n) φ → ∀ m, ct h w φ m = dl w m * Sm h w φ m :=
    fun φ hφ m => (ctSph E w n a b h φ hφ m).1
  have hsup : ∀ φ : GLw n w → ℂ, IsHecke (KGL w n) φ → ∀ m : GLw a w × GLw b w,
      (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
        φ (blk h w m (Multiplicative.toAdd q.out))).Finite :=
    fun φ hφ m => (ctSph E w n a b h φ hφ m).2
  funext m
  have hR : cv (K2 a b w) (ct h w f) (ct h w g) m =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ K2 a b w, ct h w f c.out * ct h w g (c.out⁻¹ * m) := by
    refine hintSph _ (K2 a b w) (fun z => ct h w f z * ct h w g (z⁻¹ * m)) fun k hk x => ?_
    have e : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    show ct h w f (x * k) * ct h w g ((x * k)⁻¹ * m) = ct h w f x * ct h w g (x⁻¹ * m)
    rw [e, (ct_bi h w f hf k hk x).2, (ct_bi h w g hg k⁻¹ (inv_mem hk) _).1]
  have hinv : ∀ y, ∀ k ∈ KGL w n, ∀ x, f (x * k) * g ((x * k)⁻¹ * y) = f x * g (x⁻¹ * y) := by
    intro y k hk x
    have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
    rw [e, (hf.2 k hk x).2, (hg.2 k⁻¹ (inv_mem hk) _).1]
  have hcv : ∀ y, cv (KGL w n) f g y =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b),
        ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
          f (blk h w c.out (Multiplicative.toAdd x.out)) *
            g ((blk h w c.out (Multiplicative.toAdd x.out))⁻¹ * y) := by
    intro y
    have e1 : cv (KGL w n) f g y = ∑ᶠ p : GLw n w ⧸ KGL w n, f p.out * g (p.out⁻¹ * y) :=
      hintSph _ (KGL w n) (fun z => f z * g (z⁻¹ * y)) fun k hk x => hinv y k hk x
    rw [e1]
    refine GlobalTheory.CompanionTheory.IntDec.iwasawa_sum h w (fun z => f z * g (z⁻¹ * y)) (fun k hk x => hinv y k hk x) ?_
    refine (GlobalTheory.CompanionTheory.IntDec.finite_mk_support (KGL w n) hKo f hf.1).subset fun p hp => ?_
    exact ⟨p.out, left_ne_zero_of_mul hp, QuotientGroup.out_eq' p⟩
  have hCs : {c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b) |
      ∃ Y, f (blk h w c.out Y) ≠ 0}.Finite := by
    refine GlobalTheory.CompanionTheory.IntDec.finite_lev h w _ (GlobalTheory.CompanionTheory.IntDec.finite_mk_support (KGL w n) hKo f hf.1) _ ?_
    rintro c ⟨Y, hY⟩
    exact ⟨c.out, Y, QuotientGroup.out_eq' c, _, hY, rfl⟩
  have hgR : ∀ k ∈ KGL w n, ∀ x, g (x * k) = g x := fun k hk x => (hg.2 k hk x).2
  have hv : ∀ (c : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E))
      (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))),
      g ((blk h w c Y)⁻¹ * blk h w m (Multiplicative.toAdd X)) =
        g (blk h w (c⁻¹ * m) (Multiplicative.toAdd
          (X * Multiplicative.ofAdd (-(((c⁻¹ * m).1⁻¹).val * Y * (c⁻¹ * m).2.val))))) := by
    intro c Y X
    rw [inv_blk]
    rfl
  have hS : Sm h w (cv (KGL w n) f g) m =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b),
        Sm h w f c.out * Sm h w g (c.out⁻¹ * m) := by
    unfold Sm
    simp_rw [hcv]
    refine swap3 (fun c x => f (blk h w (Quotient.out c) (Multiplicative.toAdd (Quotient.out x))))
      (fun c x X => g ((blk h w (Quotient.out c) (Multiplicative.toAdd (Quotient.out x)))⁻¹ *
        blk h w m (Multiplicative.toAdd (Quotient.out X)))) _ hCs ?_ (fun c => hsup f hf _) ?_
      (fun c => ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
        g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd (Quotient.out x)))) ?_
    · intro c hc x
      by_contra hx
      exact hc ⟨_, hx⟩
    · intro c x
      simp_rw [hv]
      exact support_translate (intMat a b w)
        (fun z => g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd z)))
        (fun z l hl => right_L h w g hgR _ z l hl) _ (hsup g hg _)
    · intro c x
      simp_rw [hv]
      exact sum_translate (intMat a b w)
        (fun z => g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd z)))
        (fun z l hl => right_L h w g hgR _ z l hl) _
  rw [hR, hct _ hfg, hS, ← smul_eq_mul, smul_finsum]
  refine finsum_congr fun c => ?_
  have e : dl w m = dl w (Quotient.out c) * dl w ((Quotient.out c)⁻¹ * m) := by
    rw [← dl_mul, mul_inv_cancel_left]
  rw [hct f hf, hct g hg, smul_eq_mul, e]
  ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

