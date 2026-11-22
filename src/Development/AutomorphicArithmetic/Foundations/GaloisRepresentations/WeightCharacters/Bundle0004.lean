import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem entry_mul_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {A B : Matrix (Fin a) (Fin a) ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖ι.symm (A i j)‖ ≤ r) (hB : ∀ i j, ‖ι.symm (B i j)‖ ≤ s) (i j : Fin a) :
    ‖ι.symm ((A * B) i j)‖ ≤ r * s := by
  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hr

theorem UpperTheory.Gal.Wt.nearSub_of :
    UpperTheory.Gal.Wt.NearSub := by
  intro l _ ι a Γ _ _ _ φ hc hI ε hε
  refine ⟨{ carrier := {g | NearOne ι ε (φ g)}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, fun g => Iff.rfl⟩
  · intro g h hg hh
    have hg' : NearOne ι ε (φ g) := hg
    have hh' : NearOne ι ε (φ h) := hh
    show NearOne ι ε (φ (g * h))
    intro i j
    have key : ((φ (g * h) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) * ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
          + (((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) := by
      rw [map_mul, Units.val_mul]
      noncomm_ring
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.add_apply, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := entry_mul_le ι hε.le zero_le_one
        (A := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
        (B := ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
        (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) (fun i j => (hI h i j).1) i j
      exact this.trans_eq (mul_one ε)
    · rw [Matrix.sub_apply]
      exact hh' i j
  · show NearOne ι ε (φ 1)
    intro i j
    rw [map_one, Units.val_one, sub_self, map_zero, norm_zero]
    exact hε.le
  · intro g hg
    have hg' : NearOne ι ε (φ g) := hg
    show NearOne ι ε (φ g⁻¹)
    intro i j
    have key : ((φ g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = -((((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
            * (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)) := by
      rw [map_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.neg_apply, map_neg, norm_neg]
    have := entry_mul_le ι zero_le_one hε.le
      (A := (((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
      (B := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
      (fun i j => (hI g i j).2) (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) i j
    exact this.trans_eq (one_mul ε)
  · have hset : ({g | NearOne ι ε (φ g)} : Set Γ)
        = ⋂ i, ⋂ j, (fun g => ι.symm (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)) ⁻¹'
            Metric.closedBall (ι.symm ((1 : Matrix (Fin a) (Fin a) ℂ) i j)) ε := by
      ext g
      simp only [Set.mem_setOf_eq, NearOne, map_sub, Set.mem_iInter, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
    show IsOpen ({g | NearOne ι ε (φ g)} : Set Γ)
    rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hc i j).isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hε.ne')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NrmAut
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.nrmAut_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.NrmAut := by
  intro hC E _ _ _ a τ C hCl n hn p hp
  obtain ⟨hpc, A, hAf, hA⟩ := hp
  let S : Submodule ℂ (UA E a → ℂ) := A.map (LinearMap.funLeft ℂ ℂ n)
  have hSf : FiniteDimensional ℂ S := inferInstance
  have hS : ∀ y, (fun g => p (n g * y)) ∈ S := fun y => ⟨_, hA y, rfl⟩
  refine ⟨fun y => ?_, S, hSf, hS⟩
  refine hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g])
    (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)
  · have he : (fun x : infU E a => p (n (g * x.1) * y)) =
        fun x : infU E a => p (n g * (cEmb τ x.1 * y)) := by
      funext x
      rw [hn.inf x.1 x.2 g, mul_assoc]
    rw [he]
    exact hpc.comp (continuous_const.mul
      (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))
  · have he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y)) := by
      funext g
      change p (n (g * x) * y) = _
      rw [hn.inf x hx g, mul_assoc]
    rw [he]
    exact hS _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_entry_mem_expLe_one_expGe_zero (h : ExpBasic) (a k : ℕ) (A B : GL (Fin a) ℂ) (i j : Fin a) :
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpLe 1 ∧
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpGe 0 := by
  obtain ⟨_, _, hmono, hmon, hconst, _⟩ := h
  have heq : (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ l : Fin a, fun z : Circle => (A : Matrix (Fin a) (Fin a) ℂ) i l *
        ((if (l:ℕ) < k then (z:ℂ) else 1) * (B : Matrix (Fin a) (Fin a) ℂ) l j) := by
    funext z
    rw [Finset.sum_apply, Units.val_mul, Units.val_mul, Matrix.mul_apply]
    congr 1
    funext l
    simp only [tor, dg, Matrix.diagonal_mul]
    split_ifs
    · simp only [Circle.toUnits]
      first
        | rfl
        | simp [unitSphereToUnits_apply_coe]
    · simp
  rw [heq]
  constructor
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).1 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hmono 0 1 (by norm_num)).1
        (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).1 using 1
      funext z
      simp [hl]
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmono 0 1 (by norm_num)).2
        (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).2 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).2 using 1
      funext z
      simp [hl]

private theorem pow_mem_expLe_expGe_of_mem (h : ExpBasic) (f : Circle → ℂ) (hf : f ∈ ExpLe 1 ∧ f ∈ ExpGe 0) (n : ℕ) :
    (fun z => f z ^ n) ∈ ExpLe (n : ℤ) ∧ (fun z => f z ^ n) ∈ ExpGe 0 := by
  obtain ⟨hmulL, hmulG, _, _, hconst, _⟩ := h
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact hconst 1
  | succ n ih =>
    have e : (fun z => f z ^ (n + 1)) = fun z => (fun z => f z ^ n) z * f z := by
      funext z
      exact pow_succ _ _
    rw [e]
    constructor
    · have := hmulL _ _ _ _ ih.1 hf.1
      push_cast
      exact this
    · have := hmulG _ _ _ _ ih.2 hf.2
      simpa using this

private theorem prod_pow_mem_expLe_sum_expGe {ι : Type} [DecidableEq ι] (h : ExpBasic) (e : ι → Circle → ℂ)
    (he : ∀ i, e i ∈ ExpLe 1 ∧ e i ∈ ExpGe 0) (d : ι → ℕ) (S : Finset ι) :
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpLe ((∑ i ∈ S, d i : ℕ) : ℤ) ∧
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpGe 0 := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero]
    exact h.2.2.2.2.1 1
  | insert x S hx ih =>
    have hp := pow_mem_expLe_expGe_of_mem h (e x) (he x) (d x)
    have e1 : (fun z => ∏ i ∈ insert x S, e i z ^ d i) =
        fun z => (fun z => e x z ^ d x) z * (fun z => ∏ i ∈ S, e i z ^ d i) z := by
      funext z
      exact Finset.prod_insert hx
    rw [e1]
    constructor
    · have := h.1 _ _ _ _ hp.1 ih.1
      rw [Finset.sum_insert hx, Nat.cast_add]
      exact this
    · have := h.2.1 _ _ _ _ hp.2 ih.2
      simpa using this

theorem UpperTheory.Gal.Wt.pevExp_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.PevExp := by
  intro h a k P A B
  classical
  let e : Fin a × Fin a → Circle → ℂ := fun p z =>
    ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p.1 p.2
  have he : ∀ p, e p ∈ ExpLe 1 ∧ e p ∈ ExpGe 0 := fun p => tor_entry_mem_expLe_one_expGe_zero h a k A B p.1 p.2
  have hsum : (fun z => pev P (A * (tor a k z * B))) =
      ∑ d ∈ P.support, fun z => MvPolynomial.coeff d P * ∏ i ∈ d.support, e i z ^ d i := by
    funext z
    rw [Finset.sum_apply]
    simp only [pev]
    rw [MvPolynomial.eval_eq]
  rw [hsum]
  constructor
  · refine Submodule.sum_mem _ fun d hd => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).1
    have hle : ((∑ i ∈ d.support, d i : ℕ) : ℤ) ≤ (P.totalDegree : ℤ) := by
      exact_mod_cast MvPolynomial.le_totalDegree hd
    have hm := (h.2.2.1 _ _ hle).1 hp
    convert Submodule.smul_mem _ (MvPolynomial.coeff d P) hm using 1
    funext z
    rfl
  · refine Submodule.sum_mem _ fun d _ => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).2
    convert Submodule.smul_mem _ (MvPolynomial.coeff d P) hp using 1
    funext z
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem pev_map {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (P' : MvPolynomial (Fin a × Fin a) (Qbar l)) (h : GL (Fin a) ℂ) :
    ι.symm (pev (MvPolynomial.map ι.toRingHom P') h) =
      MvPolynomial.eval (fun p : Fin a × Fin a => ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)) P' := by
  induction P' using MvPolynomial.induction_on with
  | C c => simp [pev]
  | add p q hp hq =>
    simp only [pev, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [pev, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hp ⊢
    rw [hp]

theorem pieces_of (hS : SepPoly) (hN : NearSub) : Pieces := by
  intro l _ ι a Γ _ _ _ _ φ hcont hint Γ' hΓ' hker ε hε
  obtain ⟨H, hHo, hH⟩ := hN l ι a Γ φ hcont hint ε hε
  set K : Subgroup Γ := H ⊓ Γ' with hK
  have hKo : IsOpen (K : Set Γ) := by
    rw [hK, Subgroup.coe_inf]
    exact hHo.inter hΓ'
  have hkerK : φ.ker ≤ K := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨(hH g).2 ?_, hker hg⟩
    intro i j
    rw [MonoidHom.mem_ker.mp hg]
    simpa using hε.le
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  let c : Γ ⧸ K → Γ := fun q => q.out
  let v : Γ → (Fin a × Fin a → Qbar l) := fun g p => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)
  have hv : Continuous v := continuous_pi fun p => hcont p.1 p.2
  have hKc : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKo
  have hinj : ∀ g g', v g = v g' → g⁻¹ * g' ∈ K := by
    intro g g' hgg
    apply hkerK
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ι.symm.injective (congrFun hgg (i, j))
  have hsep : ∀ q : Γ ⧸ K, ∃ P' : MvPolynomial (Fin a × Fin a) (Qbar l),
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∈ K}, ‖MvPolynomial.eval z P' - 1‖ ≤ ε) ∧
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∉ K}, ‖MvPolynomial.eval z P'‖ ≤ ε) := by
    intro q
    have hc1 : IsCompact (v '' {g | (c q)⁻¹ * g ∈ K}) :=
      (hKc.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hc2 : IsCompact (v '' {g | (c q)⁻¹ * g ∉ K}) :=
      (hKo.isClosed_compl.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hd : Disjoint (v '' {g | (c q)⁻¹ * g ∈ K}) (v '' {g | (c q)⁻¹ * g ∉ K}) := by
      rw [Set.disjoint_left]
      rintro z ⟨g, hg, rfl⟩ ⟨g', hg', hgg⟩
      apply hg'
      have hm := K.mul_mem hg (hinj g g' hgg.symm)
      simpa [mul_assoc] using hm
    exact hS (Qbar l) (Fin a × Fin a) _ _ hc1 hc2 hd ε hε
  choose P' hP1 hP2 using hsep
  refine ⟨Γ ⧸ K, inferInstance, c, fun q => MvPolynomial.map ι.toRingHom (P' q), ?_⟩
  intro g
  have hmem : ∀ q : Γ ⧸ K, (c q)⁻¹ * g ∈ K ↔ q = (g : Γ ⧸ K) := by
    intro q
    rw [← QuotientGroup.eq]
    simp [c]
  have h0 : (c (g : Γ ⧸ K))⁻¹ * g ∈ K := (hmem _).2 rfl
  refine ⟨(g : Γ ⧸ K), (Subgroup.mem_inf.mp h0).2, (hH _).1 (Subgroup.mem_inf.mp h0).1, ?_, ?_⟩
  · beta_reduce
    rw [map_sub, map_one, pev_map]
    exact hP1 _ _ ⟨g, h0, rfl⟩
  · intro q hq
    beta_reduce
    rw [pev_map]
    exact hP2 q _ ⟨g, fun h => hq ((hmem q).1 h), rfl⟩

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem rFin_const {a : ℕ} (c : ℂ) : RFin (fun _ : GL (Fin a) ℂ => c) := by
  refine ⟨continuous_const, Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, fun y => ?_⟩
  exact Submodule.mem_span_singleton.2 ⟨c, by funext n; simp⟩

private theorem rFin_add {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h + q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.add cq, A ⊔ B, inferInstance, fun y => ?_⟩
  have h := Submodule.add_mem_sup (mA y) (mB y)
  exact h

private theorem rFin_mul {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h * q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.mul cq, A * B, ?_, fun y => ?_⟩
  · have h1 : A.FG := (Submodule.fg_iff_finiteDimensional A).2 fA
    have h2 : B.FG := (Submodule.fg_iff_finiteDimensional B).2 fB
    exact (Submodule.fg_iff_finiteDimensional _).1 (h1.mul h2)
  · have h := Submodule.mul_mem_mul (mA y) (mB y)
    exact h

private theorem rFin_entry {a : ℕ} (i j : Fin a) :
    RFin (fun h : GL (Fin a) ℂ => (h : Matrix (Fin a) (Fin a) ℂ) i j) := by
  refine ⟨Units.continuous_val.matrix_elem i j,
    Submodule.span ℂ (Set.range fun r : Fin a => fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), fun y => ?_⟩
  have h : (fun n : GL (Fin a) ℂ => ((n * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ r, (y : Matrix (Fin a) (Fin a) ℂ) r j • fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r := by
    funext n
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private theorem rFin_of_rep {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : GL (Fin a) ℂ →* (V →ₗ[ℂ] V)) (l : V →ₗ[ℂ] ℂ) (v : V) (X : GL (Fin a) ℂ)
    (hc : Continuous fun h : GL (Fin a) ℂ => l (ρ h v)) : RFin fun n => l (ρ (X * n) v) := by
  refine ⟨hc.comp (continuous_const.mul continuous_id),
    LinearMap.range (LinearMap.pi fun n : GL (Fin a) ℂ => l ∘ₗ ρ (X * n)), inferInstance,
    fun y => ⟨ρ y v, ?_⟩⟩
  funext n
  change l (ρ (X * n) (ρ y v)) = l (ρ (X * (n * y)) v)
  rw [← mul_assoc, map_mul ρ (X * n) y]
  rfl

private theorem rFin_delta {a : ℕ} (ν : DomWeight a) (X : GL (Fin a) ℂ) : RFin fun n => delta ν (X * n) := by
  haveI : FiniteDimensional ℂ (nablaSq ℂ a ν) := inferInstance
  exact rFin_of_rep (sqRep ℂ a ν) (ev1 ν) (top ν) X (GlobalTheory.BCT.TrKer.continuous_coef_sqRep a ν (top ν) (ev1 ν))

theorem UpperTheory.Gal.Wt.rFinEx_of :
    UpperTheory.Gal.Wt.RFinEx := by
  intro a
  refine ⟨rFin_delta, fun P => ?_⟩
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : pev (MvPolynomial.C c : MvPolynomial (Fin a × Fin a) ℂ) = fun _ => c := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_const c
  | add p q hp hq =>
    have h : pev (p + q) = fun g => pev p g + pev q g := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_add hp hq
  | mul_X p n hp =>
    have h : pev (p * MvPolynomial.X n) = fun g => pev p g * (g : Matrix (Fin a) (Fin a) ℂ) n.1 n.2 := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_mul hp (rFin_entry n.1 n.2)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SumRep
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.sumRep_of :
    UpperTheory.Gal.Wt.SumRep := by
  intro E _ _ _ a S hfin hS
  classical
  obtain ⟨B₀, -, -, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E a
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E a).subtype (autU E a).ker_subtype
  have hpv : ∀ (φ : UA E a → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E a)
  let B : (UA E a → ℂ) →ₗ⋆[ℂ] (UA E a → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E a → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E a B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) h
  let b := Module.finBasis ℂ S
  have hex : ∀ i, ∃ s : Finset (Submodule ℂ (UA E a → ℂ)), (↑s ⊆ {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) ∧
      (b i : UA E a → ℂ) ∈ ⨆ U ∈ s, U :=
    fun i => Submodule.mem_sSup_iff_exists_finset.1 (hsum _ (hS _ (b i).2))
  choose s hsA hsm using hex
  let s0 := Finset.univ.biUnion s
  have hs0A : ∀ U ∈ s0, IsAutRepU U := by
    intro U hU
    obtain ⟨i, -, hi'⟩ := Finset.mem_biUnion.1 hU
    exact hsA i hi'
  obtain ⟨t, hts, hti, htS⟩ := GlobalTheory.EigenDecomp.exists_indep s0 hs0A
  refine ⟨t, fun U hU => hs0A U (hts hU), hti, ?_⟩
  intro φ hφ
  rw [htS]
  have e : φ = ∑ i, (b.repr ⟨φ, hφ⟩ i) • (b i : UA E a → ℂ) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine (iSup₂_le fun U hU => le_sSup ?_ : (⨆ U ∈ s i, U) ≤ sSup (s0 : Set (Submodule ℂ (UA E a → ℂ)))) (hsm i)
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hU⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopUpOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.topUp_of :
    UpperTheory.Gal.Wt.TopUp := by
  intro a κ b hb
  have hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := fun i j h => hb i j h
  have hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0 := by
    have hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
    rw [Matrix.det_of_upperTriangular hbt] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  let t : Fin a → ℂˣ := fun i => Units.mk0 _ (hdiag i)
  set D := diagGL ℂ a t with hD
  set u := D⁻¹ * b with hu
  have hbu : b = D * u := by rw [hu, mul_inv_cancel_left]
  have hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ) := rfl
  have hucoe : (u : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hu, Units.val_mul, hDinv]
  have hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := by
    rw [hucoe]
    exact (Matrix.blockTriangular_diagonal _).mul hbt
  have hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1 := by
    intro i
    rw [hucoe, Matrix.diagonal_mul]
    simp [t, hdiag i]
  have hfix : (sqRep ℂ a κ u) (top κ) = top κ := by
    apply Subtype.ext
    exact (factSqHighestWeight ℂ a κ).2 u hut hu1
  have hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ := by
    apply Subtype.ext
    have h := (factSqHighestWeight ℂ a κ).1 t
    have hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b := by
      rw [Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]
    rw [hc] at h
    exact h
  calc (sqRep ℂ a κ b) (top κ) = (sqRep ℂ a κ D) ((sqRep ℂ a κ u) (top κ)) := by
        rw [hbu, map_mul, Module.End.mul_apply]
    _ = chi κ b • top κ := by rw [hfix, hscal]
end

